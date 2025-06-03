using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// Representation of an expression like arrayRef`[index1, index2...] or arrayRefSet`[index1, index2...]
/// If obj is a single object, resolves to FieldLocation
/// If obj is a set of objects, resolves to set x | x in ObjectCopy :: x`[index1, index2] (IndexFieldLocation)
/// Same for sequences or multisets
/// </summary>
/// <summary>
/// The right-hand-side of an expression of the type arrayRef`[index1, index2...]
/// Denotes the memory location at this index
/// </summary>
public class IndexFieldLocationExpression : SuffixExpr, ICloneable<IndexFieldLocationExpression> {
  public Token CloseParen { get; }

  public Token OpenParen { get; }

  public List<Expression> Indices { get; }

  public IndexFieldLocationExpression(Expression lhs, Token openParen, List<Expression> indices, Token closeParen) : base(new SourceOrigin(openParen, closeParen), lhs) {
    Contract.Requires(indices.Count != 0);
    this.Indices = indices;
    this.OpenParen = openParen;
    this.CloseParen = closeParen;
  }

  public IndexFieldLocationExpression(Cloner cloner, IndexFieldLocationExpression original) : base(cloner, original) {
    Contract.Requires(original != null);
    Contract.Ensures(type == null);
    this.Indices = original.Indices.Select(cloner.CloneExpr).ToList();
    this.OpenParen = original.OpenParen;
    this.CloseParen = original.CloseParen;
    this.ResolvedExpression = original.ResolvedExpression != null
      ? cloner.CloneExpr(original.ResolvedExpression) : null;
  }

  public IndexFieldLocationExpression Clone(Cloner cloner) {
    return new IndexFieldLocationExpression(cloner, this);
  }

  public override IEnumerable<Expression> PreResolveSubExpressions => base.PreResolveSubExpressions.Concat(Indices);
  public override IEnumerable<Expression> SubExpressions => ResolvedExpression == null ? PreResolveSubExpressions : [
    ResolvedExpression
  ];
}