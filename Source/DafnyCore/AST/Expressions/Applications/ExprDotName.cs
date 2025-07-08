#nullable enable

using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// An ExprDotName desugars into either an IdentifierExpr (if the Lhs is a static name) or a MemberSelectExpr (if the Lhs is a computed expression).
/// </summary>
public class ExprDotName : SuffixExpr, ICloneable<ExprDotName> {
  public Name SuffixNameNode;
  public string SuffixName => SuffixNameNode.Value;
  public List<Type>? OptTypeArguments;

  /// <summary>
  /// Because the resolved expression only points to the final resolved declaration,
  /// but not the declaration of the Lhs, we must also include the Lhs.
  /// </summary>
  public override IEnumerable<INode> Children => ResolvedExpression == null
    ? [Lhs]
    : new[] { Lhs, ResolvedExpression };

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(SuffixName != null);
  }

  public ExprDotName Clone(Cloner cloner) {
    return new ExprDotName(cloner, this);
  }

  public ExprDotName(Cloner cloner, ExprDotName original) : base(cloner, original) {
    SuffixNameNode = new Name(cloner, original.SuffixNameNode);
    OptTypeArguments = original.OptTypeArguments?.ConvertAll(cloner.CloneType);
  }

  [SyntaxConstructor]
  public ExprDotName(IOrigin origin, Expression lhs, Name suffixNameNode, List<Type>? optTypeArguments)
    : base(origin, lhs) {
    SuffixNameNode = suffixNameNode;
    OptTypeArguments = optTypeArguments;
  }
}