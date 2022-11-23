namespace Microsoft.Dafny; 

public class VerifyIncludedFilesOption : BooleanOption {
  public static readonly VerifyIncludedFilesOption Instance = new();
  public override string LongName => "verify-included-files";

  public override string Description => @"Verify code in included files.";

  public override string PostProcess(DafnyOptions options) {
    options.VerifyAllModules = Get(options);
    return null;
  }
}
