using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public abstract class NestedMatchCase : TokenNode {
  public readonly ExtendedPattern Pat;

  protected NestedMatchCase(IOrigin origin, ExtendedPattern pat) : base(origin) {
    Contract.Requires(origin != null);
    Contract.Requires(pat != null);
    this.Pat = pat;
  }

  public void CheckLinearNestedMatchCase(Type type, ResolutionContext resolutionContext, ModuleResolver resolver) {
    Pat.CheckLinearExtendedPattern(type, resolutionContext, resolver);
  }
}