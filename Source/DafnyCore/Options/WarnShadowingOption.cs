namespace Microsoft.Dafny;

public class WarnShadowingOption : BooleanOption {
  public static readonly WarnShadowingOption Instance = new();
  public override string LongName => "warn-shadowing";

  public override string Description => @"
Emit a warning if the name of a declared variable caused another variable to be shadowed.".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    options.WarnShadowing = Get(options);
    return null;
  }
}
