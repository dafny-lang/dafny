using Microsoft.CodeAnalysis.Operations;

namespace Microsoft.Dafny;

public class OutputOption : StringOption, ILegacyOption {
  public static readonly OutputOption Instance = new();
  public override object DefaultValue => null;
  public override string LongName => "output";
  public string LegacyName => "out";
  public override string ShortName => "o";
  public override string ArgumentName => "file";
  public string Category => "Compilation options";
  public override string Description => @"      
Specify the filename and location for the generated target language
files.".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    options.DafnyPrintCompiledFile = Get(options);
    return null;
  }
}
