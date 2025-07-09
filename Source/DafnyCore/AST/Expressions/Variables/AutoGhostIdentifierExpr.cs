using System.Collections.Generic;

namespace Microsoft.Dafny;

/// <summary>
/// If an "AutoGhostIdentifierExpr" is used as the out-parameter of a ghost method or
/// a method with a ghost parameter, resolution will change the .Var's .IsGhost to true
/// automatically.  This class is intended to be used only as a communicate between the
/// parser and parts of the resolver.
/// </summary>
public class AutoGhostIdentifierExpr : IdentifierExpr, ICloneable<AutoGhostIdentifierExpr> {

  [SyntaxConstructor]
  public AutoGhostIdentifierExpr(IOrigin origin, string name)
    : base(origin, name) { }

  public AutoGhostIdentifierExpr(Cloner cloner, AutoGhostIdentifierExpr original)
    : base(cloner, original) {
  }

  public new AutoGhostIdentifierExpr Clone(Cloner cloner) {
    return new AutoGhostIdentifierExpr(cloner, this);
  }

  public override IEnumerable<Reference> GetReferences() {
    return [];
  }
}