namespace Microsoft.Dafny;

public class QuietOption : BooleanOption {
  public static readonly QuietOption Instance = new();
  public override bool Hidden => false;
  public override object DefaultValue => false;
  public override string LongName => "quiet";
  public override string Category => null;
  public override string Description => @"
false (default) - Print information such as files being written by the
    compiler to the console.
true - Don't print status of compilation to the console.";
  public override string PostProcess(DafnyOptions options) {
    options.CompileVerbose = !Get(options);
    return null;
  }
}
