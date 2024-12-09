using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// Represents an expression of the form S[I := V], where, syntactically, S, I, and V are expressions.
///
/// Successfully resolved, the expression stands for one of the following:
/// * if S is a seq<T>, then I is an integer-based index into the sequence and V is of type T
/// * if S is a map<T, U>, then I is a key of type T and V is a value of type U
/// * if S is a multiset<T>, then I is an element of type T and V has an integer-based numeric type.
///
/// Datatype updates are represented by <c>DatatypeUpdateExpr</c> nodes.
/// </summary>
public class SeqUpdateExpr : Expression, ICloneable<SeqUpdateExpr> {
  public readonly Expression Seq;
  public readonly Expression Index;
  public readonly Expression Value;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Seq != null);
    Contract.Invariant(Index != null);
    Contract.Invariant(Value != null);
  }

  public SeqUpdateExpr(Cloner cloner, SeqUpdateExpr original) : base(cloner, original) {
    Seq = cloner.CloneExpr(original.Seq);
    Index = cloner.CloneExpr(original.Index);
    Value = cloner.CloneExpr(original.Value);
  }

  public SeqUpdateExpr(IOrigin tok, Expression seq, Expression index, Expression val)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(seq != null);
    Contract.Requires(index != null);
    Contract.Requires(val != null);
    Seq = seq;
    Index = index;
    Value = val;
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return Seq;
      yield return Index;
      yield return Value;
    }
  }

  public SeqUpdateExpr Clone(Cloner cloner) {
    return new SeqUpdateExpr(cloner, this);
  }
}