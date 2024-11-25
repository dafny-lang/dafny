using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public abstract class NestedMatchCase : TokenNode {
  public readonly ExtendedPattern Pat;

  public NestedMatchCase(IOrigin tok, ExtendedPattern pat) {
    Contract.Requires(tok != null);
    Contract.Requires(pat != null);
    this.tok = tok;
    this.Pat = pat;
  }

  public void CheckLinearNestedMatchCase(Type type, ResolutionContext resolutionContext, ModuleResolver resolver) {
    Pat.CheckLinearExtendedPattern(type, resolutionContext, resolver);
  }
}