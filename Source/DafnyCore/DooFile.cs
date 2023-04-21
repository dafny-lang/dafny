using System;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.IO.Compression;
using System.Text;
using Microsoft.Dafny;
using Tomlyn;

namespace DafnyCore; 

public class DooFile {

  private const string PROGRAM_FILE_ENTRY = "program.dfy";
  
  private const string MANIFEST_FILE_ENTRY = "manifest.toml";

  public class ManifestData {
    public const string CURRENT_DOO_FILE_VERSION = "1.0";
    public string DooFileVersion { get; private set; }
  
    public string DafnyVersion { get; private set; }
    
    public Dictionary<string, object> Options { get; set; }

    public ManifestData() {
      // Only for TOML deserialization!
    }
    
    public ManifestData(DafnyOptions options) {
      DooFileVersion = CURRENT_DOO_FILE_VERSION;
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
    
    using (ZipArchive archive = ZipFile.Open(path, ZipArchiveMode.Read)) {
      ZipArchiveEntry manifestEntry = archive.GetEntry(MANIFEST_FILE_ENTRY);
      if (manifestEntry == null) {
        throw new ArgumentException(".doo file missing manifest entry");
      }
      using (var manifestStream = manifestEntry.Open()) {
        result.Manifest = ManifestData.Read(new StreamReader(manifestStream, Encoding.UTF8));
      }
      
      ZipArchiveEntry programTextEntry = archive.GetEntry(PROGRAM_FILE_ENTRY);
      if (programTextEntry == null) {
        throw new ArgumentException(".doo file missing program text entry");
      }
      using (var programTextStream = programTextEntry.Open()) {
        var reader = new StreamReader(programTextStream, Encoding.UTF8);
        result.ProgramText = reader.ReadToEnd();
      }
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
  
  public void Write(string path) {
    // Delete first, we don't want to merge with existing zips
    File.Delete(path);
    
    using ZipArchive archive = ZipFile.Open(path, ZipArchiveMode.Create);

    var manifest = archive.CreateEntry(MANIFEST_FILE_ENTRY);
    using (var manifestStream = manifest.Open()) {
      using var manifestWriter = new StreamWriter(manifestStream, Encoding.UTF8);
      Manifest.Write(manifestWriter);
    }

    var programText = archive.CreateEntry(PROGRAM_FILE_ENTRY);
    using (var programTextStream = programText.Open()) {
      using var programTextWriter = new StreamWriter(programTextStream, Encoding.UTF8);
      programTextWriter.Write(ProgramText);
    }
  }
  
}