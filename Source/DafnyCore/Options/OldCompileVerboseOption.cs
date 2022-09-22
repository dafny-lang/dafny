namespace Microsoft.Dafny;

public class OldCompileVerboseOption : BooleanOption {
  public static readonly OldCompileVerboseOption Instance = new();
  public override string LongName => "compileVerbose";
  public override bool Hidden => true;
  public override object DefaultValue => true;
  public override string Category => "Compilation options";
  public override string Description => @"
0 - Don't print status of compilation to the console.
1 (default) - Print information such as files being written by the
    compiler to the console.";
  public override string PostProcess(DafnyOptions options) {
    options.CompileVerbose = Get(options);
    return null;
  }
}
