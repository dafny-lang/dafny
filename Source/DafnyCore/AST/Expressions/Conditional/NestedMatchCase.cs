#nullable enable

namespace Microsoft.Dafny;

public abstract class NestedMatchCase : NodeWithOrigin {
  public ExtendedPattern Pat;

  [SyntaxConstructor]
  protected NestedMatchCase(IOrigin origin, ExtendedPattern pat) : base(origin) {
    Pat = pat;
  }

  public void CheckLinearNestedMatchCase(Type type, ResolutionContext resolutionContext, ModuleResolver resolver) {
    Pat.CheckLinearExtendedPattern(type, resolutionContext, resolver);
  }
}