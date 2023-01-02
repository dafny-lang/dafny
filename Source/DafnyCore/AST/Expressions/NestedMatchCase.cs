namespace Microsoft.Dafny;

public abstract class NestedMatchCase : INode {
  public readonly ExtendedPattern Pat;

  public NestedMatchCase(IToken tok, ExtendedPattern pat) {
    Contract.Requires(tok != null);
    Contract.Requires(pat != null);
    this.Tok = tok;
    this.Pat = pat;
  }

  public void CheckLinearNestedMatchCase(Type type, ResolutionContext resolutionContext, Resolver resolver) {
    Pat.CheckLinearExtendedPattern(type, resolutionContext, resolver);
  }
}