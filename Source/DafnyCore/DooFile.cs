using System;
using System.Collections.Generic;
using System.CommandLine;
using System.Configuration;
using System.IO;
using System.IO.Compression;
using System.Linq;
using System.Text;
using Microsoft.Dafny;
using Tomlyn;

namespace DafnyCore; 

public class DooFile {

  private const string ProgramFileEntry = "program.dfy";
  
  private const string ManifestFileEntry = "manifest.toml";

  public class ManifestData {
    public const string CurrentDooFileVersion = "1.0";
    public string DooFileVersion { get; private set; }
  
    public string DafnyVersion { get; private set; }
    
    public Dictionary<string, object> Options { get; set; }

    public ManifestData() {
      // Only for TOML deserialization!
    }
    
    public ManifestData(DafnyOptions options) {
      DooFileVersion = CurrentDooFileVersion;
      DafnyVersion = options.VersionNumber;
      
      // TODO: collect relevant options
    }
    
    public static ManifestData Read(TextReader reader) {
      return Toml.ToModel<ManifestData>(reader.ReadToEnd(), null, new TomlModelOptions());
    }

    public void Write(TextWriter writer) {
      writer.Write(Toml.FromModel(this, new TomlModelOptions()));
    }
  }
  
  public ManifestData Manifest { get; private set; }
  
  public string ProgramText { get; private set; }
  
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
    var pr = new Printer(tw, dafnyProgram.Options, dafnyProgram.Options.PrintMode);
    // TODO: afterResolver = true might be better, but is more likely
    // to not be a valid parseable program
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

  private static readonly List<Option> OptionsThatAffectSeparateVerification = new() {
    CommonOptionBag.UnicodeCharacters,
    PrintStmt.TrackPrintEffectsOption
  };
  
  private static readonly List<Option> OptionsThatAffectSeparateCompilation = new() {
    // Ideally this feature shouldn't affect separate compilation,
    // because it's automatically disabled on {:extern} signatures.
    // Realistically though, we don't have enough strong mechanisms to stop
    // target language code from referencing compiled internal code,
    // so to be conservative we flag this as not compatible in general.
    CommonOptionBag.OptimizeErasableDatatypeWrapper
  };

  // This should be all other options, but we explicitly list them so that
  // whenever a new option is created, we consciously analyze whether they affect separate processing. 
  private static readonly List<Option> OptionsThatDoNotAffectSeparateProcessing = new() {
  };

  private static ISet<Option> AllSupportedOptions =>
    OptionsThatAffectSeparateVerification
      .Concat(OptionsThatAffectSeparateCompilation)
      .Concat(OptionsThatDoNotAffectSeparateProcessing)
      .ToHashSet();

  static DooFile() {
    var conflicts = OptionsThatAffectSeparateVerification.Intersect(OptionsThatAffectSeparateCompilation);
    if (conflicts.Any()) {
      throw new Exception();
    }
    conflicts = OptionsThatAffectSeparateVerification.Intersect(OptionsThatDoNotAffectSeparateProcessing);
    if (conflicts.Any()) {
      throw new Exception();
    }
    conflicts = OptionsThatAffectSeparateCompilation.Intersect(OptionsThatDoNotAffectSeparateProcessing);
    if (conflicts.Any()) {
      throw new Exception();
    }
  }

  public static void CheckOptions(IEnumerable<Option> allOptions) {
    var unsupportedOptions = allOptions.Where(o => !AllSupportedOptions.Contains(o)).ToList();
    if (unsupportedOptions.Any()) {
      // throw new Exception($"Internal error - unsupported options registered: {{{string.Join(", ", unsupportedOptions)}}}");
    }
  }
}
