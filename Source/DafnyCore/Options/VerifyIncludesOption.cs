namespace Microsoft.Dafny; 

public class NoVerifyIncludesOption : BooleanOption {
  public static readonly NoVerifyIncludesOption Instance = new();
  public override string LongName => "verify-includes";

  public override string Description => @"Verify code in included files.";

  public override string PostProcess(DafnyOptions options) {
    options.VerifyAllModules = Get(options);
    return null;
  }
}
