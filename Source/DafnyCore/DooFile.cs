using System.CommandLine;
using System.IO;
using System.IO.Compression;
using System.Text;
using Microsoft.Dafny;

namespace DafnyCore; 

public class DooFile {
  
  public string DooFileVersion { get; private set; }
  
  public string DafnyVersion { get; private set; }
  
  public string ProgramText { get; private set; }
  
  // TODO: Correct form of checking this between packages.
  // If we store ALL options, then what do we do when we add an option?
  public DafnyOptions Options { get; private set; }

  public static DooFile Load(string path) {
    var result = new DooFile();
    
    using (ZipArchive archive = ZipFile.Open(path, ZipArchiveMode.Read)) {
      ZipArchiveEntry programTextEntry = archive.GetEntry("Program.dfy");
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
    // TODO: afterResolver = true is probably better but more likely
    // to not be a valid parseable program
    pr.PrintProgram(dafnyProgram, false);
    ProgramText = tw.ToString();
    Options = dafnyProgram.Options;
  }

  private DooFile() {
  }
  
  public void Write(string path) {
    // Delete first, we don't want to merge with existing zips
    File.Delete(path);
    
    using ZipArchive archive = ZipFile.Open(path, ZipArchiveMode.Create);
    
    ZipArchiveEntry programText = archive.CreateEntry("Program.dfy");
    using var programTextStream = programText.Open();
    using var writer = new StreamWriter(programTextStream, Encoding.UTF8);
    writer.Write(ProgramText);
  }
  
}