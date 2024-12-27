using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public abstract class NestedMatchCase : TokenNode {
  public readonly ExtendedPattern Pat;

  public NestedMatchCase(IOrigin origin, ExtendedPattern pat) {
    Contract.Requires(origin != null);
    Contract.Requires(pat != null);
    this.origin = origin;
    this.Pat = pat;
  }

  public void CheckLinearNestedMatchCase(Type type, ResolutionContext resolutionContext, ModuleResolver resolver) {
    Pat.CheckLinearExtendedPattern(type, resolutionContext, resolver);
  }
}