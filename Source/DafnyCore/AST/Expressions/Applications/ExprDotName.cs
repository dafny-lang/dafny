using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// An ExprDotName desugars into either an IdentifierExpr (if the Lhs is a static name) or a MemberSelectExpr (if the Lhs is a computed expression).
/// </summary>
public class ExprDotName : SuffixExpr, ICloneable<ExprDotName> {
  public readonly string SuffixName;
  public readonly List<Type> OptTypeArguments;

  /// <summary>
  /// Because the resolved expression only points to the final resolved declaration,
  /// but not the declaration of the Lhs, we must also include the Lhs.
  /// </summary>
  public override IEnumerable<Node> Children => ResolvedExpression == null
    ? new[] { Lhs }
    : new[] { Lhs, ResolvedExpression };

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(SuffixName != null);
  }

  public ExprDotName Clone(Cloner cloner) {
    return new ExprDotName(cloner, this);
  }

  public ExprDotName(Cloner cloner, ExprDotName original) : base(cloner, original) {
    SuffixName = original.SuffixName;
    OptTypeArguments = original.OptTypeArguments?.ConvertAll(cloner.CloneType);
  }

  public ExprDotName(IToken tok, Expression obj, string suffixName, List<Type> optTypeArguments)
    : base(tok, obj) {
    Contract.Requires(tok != null);
    Contract.Requires(obj != null);
    Contract.Requires(suffixName != null);
    this.SuffixName = suffixName;
    OptTypeArguments = optTypeArguments;
  }
}