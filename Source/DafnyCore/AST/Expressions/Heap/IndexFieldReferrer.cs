using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// The right-hand-side of an expression of the type arrayRef`[index1, index2...]
/// Denotes the memory location at this index
/// </summary>
public class IndexFieldReferrer: Expression, ICloneable<IndexFieldReferrer> {

  public Token CloseParen { get; set; }

  public Token OpenParen { get; set; }

  public List<ActualBinding> Indices { get; set; }
  
  public IndexFieldReferrer(Token openParen, List<ActualBinding> indices, Token closeParen) : base(openParen) {
    Contract.Requires(indices.Count != 0);
    this.Indices = indices;
    this.OpenParen = openParen;
    this.CloseParen = closeParen;
  }

  public IndexFieldReferrer(Cloner cloner, IndexFieldReferrer original) : base(cloner, original)
  {
    Contract.Requires(original != null);
    Contract.Ensures(type == null);
    this.Indices = original.Indices;
    this.OpenParen = original.OpenParen;
    this.CloseParen = original.CloseParen;
  }

  public IndexFieldReferrer Clone(Cloner cloner) {
    return new IndexFieldReferrer(cloner, this);
  }
}