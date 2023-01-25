using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public abstract class NestedMatchCase : RangeNode {
  public readonly ExtendedPattern Pat;

  public NestedMatchCase(RangeToken tok, ExtendedPattern pat) : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(pat != null);
    this.Pat = pat;
  }

  public void CheckLinearNestedMatchCase(Type type, ResolutionContext resolutionContext, Resolver resolver) {
    Pat.CheckLinearExtendedPattern(type, resolutionContext, resolver);
  }
}