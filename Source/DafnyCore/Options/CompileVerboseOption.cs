namespace Microsoft.Dafny;

public class CompileVerboseOption : BooleanOption {
  public static readonly CompileVerboseOption Instance = new();
  public override bool Hidden => false;
  public override object DefaultValue => false;
  public override string LongName => "compile-verbose";
  public override string Description => @"
false (default) - don't print status of compilation to the console
true - print information such as files being written by
    the compiler to the console";
  public override string PostProcess(DafnyOptions options) {
    options.CompileVerbose = !Get(options);
    return null;
  }
}