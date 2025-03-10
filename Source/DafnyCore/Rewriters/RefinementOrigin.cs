using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class RefinementOrigin : NestedOrigin {
  public readonly ModuleDefinition InheritingModule;


  public RefinementOrigin(IOrigin refineeOrigin, ModuleDefinition inheritingModule)
    : base(refineeOrigin, inheritingModule.Origin, "refining module") {
    Contract.Requires(refineeOrigin != null);
    Contract.Requires(inheritingModule != null);
    this.InheritingModule = inheritingModule;
  }

  public override string ToString() {
    return $"refinement of {WrappedOrigin} by {InheritingModule.Name}";
  }

  public override bool IsCopy => true;

  public override bool IsInherited(ModuleDefinition module) {
    return InheritingModule == module;
  }
}