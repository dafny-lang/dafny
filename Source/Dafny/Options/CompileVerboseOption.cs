namespace Microsoft.Dafny;

public class CompileVerboseOption : BooleanOption {
  public static readonly CompileVerboseOption Instance = new();
  public override bool Hidden => true;
  public override object DefaultValue => true;
  public override string LongName => "compileVerbose";
  public override string Category => "Compilation options";
  public override string Description => @"
0 - don't print status of compilation to the console
1 (default) - print information such as files being written by
    the compiler to the console";
  public override string PostProcess(DafnyOptions options) {
    options.CompileVerbose = Get(options);
    return null;
  }
}