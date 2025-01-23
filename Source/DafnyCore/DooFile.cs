#nullable enable

using System;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.IO.Compression;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using DafnyCore.Options;
using Microsoft.Dafny;
using Tomlyn;
using Tomlyn.Helpers;
using Tomlyn.Model;

namespace DafnyCore;

// Model class for the .doo file format for Dafny libraries.
// Contains the validation logic for safely consuming libraries as well.
public class DooFile {
  public const string Extension = ".doo";

  private const string ProgramFileEntry = "program";

  private const string ManifestFileEntry = "manifest.toml";

  public class ManifestData {
    public const string CurrentDooFileVersion = "1.0";
    public string DooFileVersion { get; set; }

    public string DafnyVersion { get; set; }

    public string? SolverIdentifier { get; set; }
    public string? SolverVersion { get; set; }

    public Dictionary<string, object> Options { get; set; }

    static ManifestData() {
      CommonOptionBag.EnsureStaticConstructorHasRun();
    }

    public ManifestData() {
      // Only for TOML deserialization!
      DooFileVersion = null!;
      DafnyVersion = null!;
      Options = null!;
    }

    public ManifestData(DafnyOptions options) {
      DooFileVersion = CurrentDooFileVersion;
      DafnyVersion = options.VersionNumber;

      SolverIdentifier = options.SolverIdentifier;
      // options.SolverVersion may be null (if --no-verify is used for example)
      SolverVersion = options.SolverVersion?.ToString();

      Options = new Dictionary<string, object>();
      foreach (var option in OptionRegistry.GlobalOptions.Concat(OptionRegistry.ModuleOptions)) {
        if (option == CommonOptionBag.Libraries) {
          // We don't want to serialize the FileInfo objects of this option
          // For now we add an option specific exception here so we do not need to change
          // the option registration system.
          // When improve soundness through https://github.com/dafny-lang/dafny/issues/5335
          // Then we'll get back to this
          continue;
        }
        var optionValue = options.Get((dynamic)option);
        if (option == CommonOptionBag.QuantifierSyntax) {
          switch (optionValue) {
            case QuantifierSyntaxOptions.Version4:
              optionValue = "4";
              break;
            case QuantifierSyntaxOptions.Version3:
              optionValue = "3";
              break;
          }
        }
        Options.Add(option.Name, optionValue);
      }
    }

    public static ManifestData Read(TextReader reader) {
      return Toml.ToModel<ManifestData>(reader.ReadToEnd(), null, new TomlModelOptions());
    }

    public void Write(TextWriter writer) {
      var content = Toml.FromModel(this, new TomlModelOptions() {
        ConvertToToml = obj => {
          if (obj is Enum) {
            TomlFormatHelper.ToString(obj.ToString()!, TomlPropertyDisplayKind.Default);
            return obj.ToString();
          }

          return obj;
        }
      }).Replace("\r\n", "\n");
      writer.Write(content);
    }
  }

  public ManifestData Manifest { get; set; }

  public string ProgramText { get; set; }

  public static async Task<DooFile> Read(string path) {
    using var archive = ZipFile.Open(path, ZipArchiveMode.Read);
    return await Read(archive);
  }

  public static async Task<DooFile> Read(Stream stream) {
    using var archive = new ZipArchive(stream);
    return await Read(archive);
  }

  private static async Task<DooFile> Read(ZipArchive archive) {

    var manifestEntry = archive.GetEntry(ManifestFileEntry);
    if (manifestEntry == null) {
      throw new ArgumentException(".doo file missing manifest entry");
    }

    ManifestData manifest;
    await using (var manifestStream = manifestEntry.Open()) {
      manifest = ManifestData.Read(new StreamReader(manifestStream, Encoding.UTF8));
    }

    var programTextEntry = archive.GetEntry(ProgramFileEntry);
    if (programTextEntry == null) {
      throw new ArgumentException(".doo file missing program text entry");
    }

    string programText;
    await using (var programTextStream = programTextEntry.Open()) {
      var reader = new StreamReader(programTextStream, Encoding.UTF8);
      programText = await reader.ReadToEndAsync();
    }

    var result = new DooFile(manifest, programText);
    return result;
  }

  public DooFile(Program dafnyProgram) {
    var tw = new StringWriter {
      NewLine = "\n"
    };
    var pr = new Printer(tw, dafnyProgram.Options, PrintModes.Serialization);
    // afterResolver is false because we don't yet have a way to safely skip resolution
    // when reading the program back into memory.
    // It's probably worth serializing a program in a more efficient way first
    // before adding that feature.
    pr.PrintProgram(dafnyProgram, false);
    ProgramText = tw.ToString();
    Manifest = new ManifestData(dafnyProgram.Options);
  }

  public DooFile(ManifestData manifest, string programText) {
    Manifest = manifest;
    ProgramText = programText;
  }

  /// <summary>
  /// Returns the options as specified by the DooFile
  /// </summary>
  public DafnyOptions? Validate(ErrorReporter reporter, Uri file, DafnyOptions options, IOrigin origin) {
    if (!options.UsingNewCli) {
      reporter.Error(MessageSource.Project, origin,
        $"cannot load {options.GetPrintPath(file.LocalPath)}: .doo files cannot be used with the legacy CLI");
      return null;
    }

    if (options.VersionNumber != Manifest.DafnyVersion) {
      reporter.Error(MessageSource.Project, origin,
        $"cannot load {options.GetPrintPath(file.LocalPath)}: it was built with Dafny {Manifest.DafnyVersion}, which cannot be used by Dafny {options.VersionNumber}");
      return null;
    }

    return CheckAndGetLibraryOptions(reporter, file, options, origin, Manifest.Options);
  }

  public static DafnyOptions? CheckAndGetLibraryOptions(ErrorReporter reporter,
    Uri libraryFile,
    DafnyOptions options, IOrigin origin,
    IDictionary<string, object> libraryOptions) {
    var result = new DafnyOptions(options);
    var success = true;

    var relevantOptions = options.Options.OptionArguments.Keys.ToHashSet();
    foreach (var option in OptionRegistry.GlobalOptions.Concat(OptionRegistry.ModuleOptions)) {
      // It's important to only look at the options the current command uses,
      // because other options won't be initialized to the correct default value.
      // See CommandRegistry.Create().
      if (!relevantOptions.Contains(option)) {
        continue;
      }
      var localValue = options.Get(option);

      object? libraryValue;
      if (libraryOptions.TryGetValue(option.Name, out var manifestValue)) {
        var printTomlValue = DafnyProject.PrintTomlOptionToCliValue(libraryFile, manifestValue, option);
        var parseResult = option.Parse(printTomlValue.ToArray());
        if (parseResult.Errors.Any()) {
          reporter.Error(MessageSource.Project, origin, $"could not parse value '{manifestValue}' for option '{option.Name}' that has type '{option.ValueType.Name}'");
          return null;
        }
        // By using the dynamic keyword, we can use the generic version of GetValueForOption which does type conversion,
        // which is sadly not accessible without generics.
        libraryValue = parseResult.GetValueForOption((dynamic)option);
      } else {
        // This else can occur because Tomlyn will drop aggregate properties with no values.
        // When this happens, use the default value
        libraryValue = option.Parse("").GetValueForOption(option)!;
      }

      result.Options.OptionArguments[option] = libraryValue;
      result.ApplyBinding(option);
      var prefix = $"cannot load {options.GetPrintPath(libraryFile.LocalPath)}";
      var checkpasses = OptionRegistry.GlobalCheck(option)?.Invoke(reporter, origin, prefix, option, localValue, libraryValue) ?? true;
      success = success && checkpasses;
    }

    if (!success) {
      return null;
    }

    return result;
  }

  public void Write(ConcreteSyntaxTree wr) {
    var manifestWr = wr.NewFile(ManifestFileEntry);
    using var manifestWriter = new StringWriter();
    Manifest.Write(manifestWriter);
    manifestWr.Write(manifestWriter.ToString().Replace("\r\n", "\n"));

    var programTextWr = wr.NewFile(ProgramFileEntry);
    programTextWr.Write(ProgramText);
  }

  public void Write(string path) {
    // Delete first, we don't want to merge with existing zips
    File.Delete(path);

    using var archive = ZipFile.Open(path, ZipArchiveMode.Create);

    var manifest = archive.CreateEntry(ManifestFileEntry);
    using (var manifestStream = manifest.Open()) {
      using var manifestWriter = new StreamWriter(manifestStream, Encoding.UTF8);
      Manifest.Write(manifestWriter);
    }

    var programText = archive.CreateEntry(ProgramFileEntry);
    using (var programTextStream = programText.Open()) {
      using var programTextWriter = new StreamWriter(programTextStream, Encoding.UTF8);
      programTextWriter.Write(ProgramText);
    }
  }

}
