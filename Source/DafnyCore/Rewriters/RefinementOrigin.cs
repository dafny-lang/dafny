using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class RefinementOrigin : OriginWrapper {
  public readonly ModuleDefinition InheritingModule;


  public RefinementOrigin(IOrigin tok, ModuleDefinition m)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(m != null);
    this.InheritingModule = m;
  }

  public override string ToString() {
    return $"refinement of {WrappedToken} by {InheritingModule.Name}";
  }

  public override bool IsCopy => true;

  public override bool IsInherited(ModuleDefinition m) {
    return InheritingModule == m;
  }

  public override string Filepath => WrappedToken.Filepath + "[" + InheritingModule.Name + "]";
}