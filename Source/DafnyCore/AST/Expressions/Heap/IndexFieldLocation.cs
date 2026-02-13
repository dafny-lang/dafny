using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// The right-hand-side of an expression of the type arrayRef`[index1, index2...]
/// Denotes the memory location at this index
/// </summary>
public class IndexFieldLocation : Expression, ICloneable<IndexFieldLocation> {
  public Expression ResolvedArrayCopy { get; }
  public Token CloseParen { get; }
  public Token OpenParen { get; }
  public List<Expression> Indices { get; }

  public IndexFieldLocation(Expression resolvedArrayCopy, Token openParen, List<Expression> indices, Token closeParen) : base(new SourceOrigin(openParen, closeParen)) {
    Contract.Requires(indices.Count != 0);
    this.ResolvedArrayCopy = resolvedArrayCopy;
    this.Indices = indices;
    this.OpenParen = openParen;
    this.CloseParen = closeParen;
  }

  public IndexFieldLocation(Cloner cloner, IndexFieldLocation original) : base(cloner, original) {
    Contract.Requires(original != null);
    Contract.Ensures(type == null);
    this.ResolvedArrayCopy = cloner.CloneExpr(original.ResolvedArrayCopy);
    this.Indices = original.Indices.Select(cloner.CloneExpr).ToList();
    this.OpenParen = original.OpenParen;
    this.CloseParen = original.CloseParen;
  }

  public IndexFieldLocation Clone(Cloner cloner) {
    return new IndexFieldLocation(cloner, this);
  }

  // objectCopy is not part of it because it's only used for resolution
  public override IEnumerable<Expression> SubExpressions => Indices;
}