using System;
using System.Collections.Generic;
using System.CommandLine;
using System.Configuration;
using System.IO;
using System.IO.Compression;
using System.Linq;
using System.Text;
using Microsoft.Dafny;
using Microsoft.Dafny.Auditor;
using Tomlyn;

namespace DafnyCore; 

// Model class for the .doo file format for Dafny libraries.
// Contains the validation logic for safely consuming libraries as well.
public class DooFile {

  private const string ProgramFileEntry = "program.dfy";
  
  private const string ManifestFileEntry = "manifest.toml";

  public class ManifestData {
    public const string CurrentDooFileVersion = "1.0";
    public string DooFileVersion { get; set; }
  
    public string DafnyVersion { get; set; }

    public string SolverIdentifier { get; set; }
    public string SolverVersion { get; set; }
    
    public Dictionary<string, object> Options { get; set; }

    public ManifestData() {
      // Only for TOML deserialization!
    }
    
    public ManifestData(DafnyOptions options) {
      DooFileVersion = CurrentDooFileVersion;
      DafnyVersion = options.VersionNumber;

      SolverIdentifier = options.SolverIdentifier;
      SolverVersion = options.SolverVersion.ToString();
      
      Options = new Dictionary<string, object>();
      foreach (var (option, check) in OptionChecks) {
        if (check != NoOpOptionCheck) {
          options.Options.OptionArguments.TryGetValue(option, out var optionValue);
          Options.Add(option.Name, optionValue);
        }
      }
    }
    
    public static ManifestData Read(TextReader reader) {
      return Toml.ToModel<ManifestData>(reader.ReadToEnd(), null, new TomlModelOptions());
    }

    public void Write(TextWriter writer) {
      writer.Write(Toml.FromModel(this, new TomlModelOptions()));
    }
  }
  
  public ManifestData Manifest { get; set; }
  
  public string ProgramText { get; set; }
  
  public static DooFile Read(string path) {
    var result = new DooFile();

    using var archive = ZipFile.Open(path, ZipArchiveMode.Read);
    var manifestEntry = archive.GetEntry(ManifestFileEntry);
    if (manifestEntry == null) {
      throw new ArgumentException(".doo file missing manifest entry");
    }
    using (var manifestStream = manifestEntry.Open()) {
      result.Manifest = ManifestData.Read(new StreamReader(manifestStream, Encoding.UTF8));
    }
      
    var programTextEntry = archive.GetEntry(ProgramFileEntry);
    if (programTextEntry == null) {
      throw new ArgumentException(".doo file missing program text entry");
    }
    using (var programTextStream = programTextEntry.Open()) {
      var reader = new StreamReader(programTextStream, Encoding.UTF8);
      result.ProgramText = reader.ReadToEnd();
    }

    return result;
  }

  public DooFile(Program dafnyProgram) {
    var tw = new StringWriter();
    var pr = new Printer(tw, dafnyProgram.Options, PrintModes.DllEmbed);
    // afterResolver is false because we don't yet have a way to safely skip resolution
    // when reading the program back into memory.
    // It's probably worth serializing a program in a more efficient way first
    // before adding that feature.
    pr.PrintProgram(dafnyProgram, false);
    ProgramText = tw.ToString();
    Manifest = new ManifestData(dafnyProgram.Options);
  }

  private DooFile() {
  }

  public void Write(ConcreteSyntaxTree wr) {
    var manifestWr = wr.NewFile(ManifestFileEntry);
    using var manifestWriter = new StringWriter();
    Manifest.Write(manifestWriter);
    manifestWr.Write(manifestWriter.ToString());
    
    var programTextWr = wr.NewFile(ProgramFileEntry);
    programTextWr.Write(ProgramText);
  }
  
  public void Write(string path) {
    // Delete first, we don't want to merge with existing zips
    File.Delete(path);
    
    using ZipArchive archive = ZipFile.Open(path, ZipArchiveMode.Create);

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

  // Partitioning of all options into subsets that must be recorded in a .doo file
  // to guard against unsafe usage.
  // Note that legacy CLI options are not as cleanly enumerated and therefore
  // more difficult to completely categorize, which is the main reason the DooBackend
  // is restricted to only the new CLI.

  private static readonly Dictionary<Option, OptionCheck> OptionChecks = new();

  public delegate bool OptionCheck(DafnyOptions options, Option option, object localValue, string libraryFile, object libraryValue);

  public static bool CheckOptionMatches(DafnyOptions options, Option option, object localValue, string libraryFile, object libraryValue) {
    if (localValue != libraryValue) {
      options.Printer.ErrorWriteLine(Console.Out, $"cannot use {libraryFile}: {option.Name} is set locally to {localValue}, but the library was build with {libraryValue}");
      return false;
    }

    return true;
  }
  
  public static bool NoOpOptionCheck(DafnyOptions options, Option option, object localValue, string libraryFile, object libraryValue) {
    return true;
  }
  
  public static void RegisterLibraryChecks(IDictionary<Option, OptionCheck> checks = null, IEnumerable<Option> noChecksNeeded = null) {
    if (checks != null) {
      foreach (var (option, check) in checks) {
        OptionChecks.Add(option, check);
      }
    }

    if (noChecksNeeded != null) {
      foreach (var option in noChecksNeeded) {
        OptionChecks.Add(option, NoOpOptionCheck);
      }
    }
  }
  
  public static void CheckOptions(IEnumerable<Option> allOptions) {
    var unsupportedOptions = allOptions.ToHashSet().Where(o => !OptionChecks.ContainsKey(o)).ToList();
    if (unsupportedOptions.Any()) {
      throw new Exception($"Internal error - unsupported options registered: {{\n{string.Join(",\n", unsupportedOptions)}\n}}");
    }
  }
}
