using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class IdentifierExpr : Expression, IHasReferences, ICloneable<IdentifierExpr> {
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Name != null);
  }

  public readonly string Name;
  [FilledInDuringResolution] public IVariable Var;

  public string DafnyName => Tok.line > 0 ? Origin.PrintOriginal() : Name;

  public IdentifierExpr(IOrigin tok, string name)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Name = name;
  }
  /// <summary>
  /// Constructs a resolved IdentifierExpr.
  /// </summary>
  public IdentifierExpr(IOrigin tok, IVariable v)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(v != null);
    Name = v.Name;
    Var = v;
    Type = v.Type;
  }

  public IdentifierExpr Clone(Cloner cloner) {
    return new IdentifierExpr(cloner, this);
  }

  public IdentifierExpr(Cloner cloner, IdentifierExpr original) : base(cloner, original) {
    Name = original.Name;

    if (cloner.CloneResolvedFields) {
      Var = cloner.CloneIVariable(original.Var, true);
    }
  }

  /// <summary>
  /// Returns whether or not "expr" is an IdentifierExpr for "variable".
  /// </summary>
  public static bool Is(Expression expr, IVariable variable) {
    return expr.Resolved is IdentifierExpr identifierExpr && identifierExpr.Var == variable;
  }

  public IEnumerable<Reference> GetReferences() {
    return Enumerable.Repeat(new Reference(Tok, Var), 1);
  }

  public override IEnumerable<INode> Children { get; } = Enumerable.Empty<Node>();
}

/// <summary>
/// An implicit identifier is used in the context of a ReturnStmt tacetly
/// assigning a value to a Method's out parameter.
/// </summary>
public class ImplicitIdentifierExpr : IdentifierExpr {
  public ImplicitIdentifierExpr(IOrigin tok, string name)
    : base(tok, name) { }

  /// <summary>
  /// Constructs a resolved implicit identifier.
  /// </summary>
  public ImplicitIdentifierExpr(IOrigin tok, IVariable v)
    : base(tok, v) { }

  public override bool IsImplicit => true;
}