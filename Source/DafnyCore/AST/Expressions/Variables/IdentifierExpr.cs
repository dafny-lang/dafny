using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class IdentifierExpr : Expression, IHasUsages, ICloneable<IdentifierExpr> {
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Name != null);
  }

  public readonly string Name;
  [FilledInDuringResolution] public IVariable Var;

  public string DafnyName => tok.line > 0 ? RangeToken.PrintOriginal() : Name;

  public IdentifierExpr(IToken tok, string name)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Name = name;
  }
  /// <summary>
  /// Constructs a resolved IdentifierExpr.
  /// </summary>
  public IdentifierExpr(IToken tok, IVariable v)
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

  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations() {
    return Enumerable.Repeat(Var, 1);
  }

  public IToken NameToken => tok;
  public override IEnumerable<Node> Children { get; } = Enumerable.Empty<Node>();
}

/// <summary>
/// An implicit identifier is used in the context of a ReturnStmt tacetly
/// assigning a value to a Method's out parameter.
/// </summary>
public class ImplicitIdentifierExpr : IdentifierExpr {
  public ImplicitIdentifierExpr(IToken tok, string name)
    : base(tok, name) { }

  /// <summary>
  /// Constructs a resolved implicit identifier.
  /// </summary>
  public ImplicitIdentifierExpr(IToken tok, IVariable v)
    : base(tok, v) { }

  public override bool IsImplicit => true;
}