using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// The right-hand-side of an expression of the type arrayRef`[index1, index2...]
/// Denotes the memory location at this index
/// </summary>
public class IndexFieldReferrer: Expression, ICloneable<IndexFieldReferrer> {
  // Because memory locations are tuples, this is just a copy of the expression so that we can determine if
  // it's legit to 
  public Expression ObjectCopy { get; }

  public Token CloseParen { get; }

  public Token OpenParen { get; }

  public List<ActualBinding> Indices { get; }
  
  public IndexFieldReferrer(Expression objectCopy, Token openParen, List<ActualBinding> indices, Token closeParen) : base(new SourceOrigin(openParen, closeParen)) {
    Contract.Requires(indices.Count != 0);
    this.ObjectCopy = objectCopy;
    this.Indices = indices;
    this.OpenParen = openParen;
    this.CloseParen = closeParen;
  }

  public IndexFieldReferrer(Cloner cloner, IndexFieldReferrer original) : base(cloner, original)
  {
    Contract.Requires(original != null);
    Contract.Ensures(type == null);
    this.ObjectCopy = original.ObjectCopy;
    this.Indices = original.Indices;
    this.OpenParen = original.OpenParen;
    this.CloseParen = original.CloseParen;
  }

  public IndexFieldReferrer Clone(Cloner cloner) {
    return new IndexFieldReferrer(cloner, this);
  }

  // objectCopy is not part of it because it's only used for resolution
  public override IEnumerable<Expression> SubExpressions => Indices.Select(index => index.Actual);
}