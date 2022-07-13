
include "../../Test/libraries/src/JSON/Stacks.dfy"

module {:options "/functionSyntax:4"} MetaSeq {

  import opened Stacks

  datatype SeqExpr<T> = Empty | Direct(a: seq<T>) | Concat(left: SeqExpr<T>, right: SeqExpr<T>, length: nat) {

    predicate Valid() {
      match this
      case Concat(left, right, length) => 
        && left.Valid()
        && right.Valid()
        && left.Length() + right.Length() == length
      case _ => true
    }

    function Length(): nat {
      match this
      case Empty => 0
      case Direct(a) => |a|
      case Concat(_, _, length) => length
    }

    function At(i: nat): T 
      requires Valid()
      requires i < Length()
    {
      Value()[i]
    }

    function Concatenate(s: SeqExpr<T>): SeqExpr<T> {
      Concat(this, s, Length() + s.Length())
    }

    function Value(): seq<T> 
      requires Valid()
      ensures |Value()| == Length()
    {
      match this
      case Empty => []
      case Direct(a) => a
      case Concat(left, right, _) => left.Value() + right.Value()
    }
  }

  function CalcConcat<T>(left: SeqExpr<T>, right: SeqExpr<T>, length: nat): (result: SeqExpr<T>)
    requires left.Valid()
    requires right.Valid()
    ensures result.Valid()
  {
    Direct(left.Value() + right.Value())
  } by method {
    var builder: SeqBuilder<T> := new SeqBuilder(length);
    var toVisit := new Stack<SeqExpr<T>>(Empty);
    :- expect toVisit.Push(right);
    :- expect toVisit.Push(left);

    ghost var n: nat := length;
    while 0 < toVisit.size
      invariant toVisit.Valid?()
      invariant fresh(toVisit)
      invariant fresh(toVisit.data)
      decreases n
    {
      // TODO: Have to add Pop() to Stacks.dfy
      var next := toVisit.Pop();
      assert fresh(toVisit.data);

      match next {
        case Concat(nextLeft, nextRight, _) => {
          :- expect toVisit.Push(nextRight);
          :- expect toVisit.Push(nextLeft);
        }
        case _ => {
          builder.Append(next.Value());
        }
      }

      Assume(n > 0);
      n := n - 1;
    }
    
    var v := builder.Value();
    Assume(v == left.Value() + right.Value());
    return Direct(v);
  }

  lemma {:axiom} Assume(p: bool) ensures p

  // TODO: Make this an extern. How to monomorphize?
  class SeqBuilder<T> {
    var s: seq<T>

    constructor(length: nat) 
      ensures Value() == []
    {
      s := [];
    }

    method Append(t: seq<T>) 
      modifies this
      ensures Value() == old(Value()) + t
    {
      s := s + t;
    }

    function Value(): seq<T> reads this {
      s
    }
  }

  trait {:termination false} Validatable {
    // Ghost state tracking the common set of objects most
    // methods need to read.
    ghost var Repr: set<object>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr

    // Convenience predicate for when your object's validity depends on one
    // or more other objects.
    ghost predicate ValidComponent(component: Validatable)
      reads this, Repr 
    {
      && component in Repr
      && component.Repr <= Repr
      && this !in component.Repr
      && component.Valid()
    }

    // Convenience predicate, since you often want to assert that 
    // new objects in Repr are fresh as well in most postconditions.
    twostate predicate ValidAndDisjoint()
      reads this, Repr
    {
      Valid() && fresh(Repr - old(Repr))
    }
  }

  trait Seq<T> extends Validatable {
    ghost const value: seq<T>
    
    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr

    method Value() returns (s: seq<T>)
      requires Valid()
      ensures s == value

    function Length(): nat
      requires Valid()
      reads Repr

    method At(i: nat) returns (t: T)
      requires Valid()
      requires i < Length()
      modifies Repr

    method Concatenate(s: Seq<T>) returns (l: Seq<T>)
      requires Valid() && s.Valid()
      ensures l.Valid()
  }

  // class ArraySeq<T> extends Seq<T> {
  //   const values: array<T>

  //   constructor(s: seq<T>) {
  //     values := new T[|s|] (i requires 0 <= i < |s| => s[i]);
  //   }
  // }

  // TODO: I THINK this can be a SeqExpr too...
  class LazySeq<T> extends Seq<T> {
    const length: nat
    const exprBox: AtomicBox<SeqExpr<T>>
    
    constructor(expr: SeqExpr<T>) 
      requires expr.Valid()
      ensures Valid()
      ensures this.value == expr.Value()
    {
      this.length := expr.Length();
      this.exprBox := new AtomicBox(expr, ((e: SeqExpr<T>) => e.Valid() && e.Value() == expr.Value()));

      this.Repr := {this};
      this.value := expr.Value();
    }

    ghost predicate Valid() 
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      && Repr == {this}
      && length == |value|
      && exprBox.inv == ((e: SeqExpr<T>) => e.Valid() && e.Value() == value)
    }

    method Value() returns (s: seq<T>)
      requires Valid()
      ensures s == value
    {
      var expr := Force();
      return expr.Value();
    }

    function Length(): nat 
      requires Valid()
      reads Repr
    {
      length
    }

    method Concatenate(rhs: Seq<T>) returns (l: Seq<T>) 
      requires Valid() && rhs.Valid()
      ensures l.Valid()
    {
      var expr := exprBox.Get();
      var rhsExpr: SeqExpr<T>;
      if (rhs as Seq<T>) is LazySeq<T> {
        var lazyS := (rhs as Seq<T>) as LazySeq<T>;
        rhsExpr := lazyS.exprBox.Get();
      } else {
        var rhsValue := rhs.Value();
        rhsExpr := Direct(rhsValue);
      }
      var sLength := rhsExpr.Length();
      l := new LazySeq(Concat(expr, rhsExpr, expr.Length() + sLength));
    }

    method Force() returns (expr: SeqExpr<T>)
      requires Valid()
      ensures Valid()
      ensures expr.Valid()
      ensures expr.Value() == value
    {
      expr := exprBox.Get();
      match expr
      case Concat(left, right, length) => {
        expr := CalcConcat(left, right, length);
        exprBox.Put(expr);
      }
      case _ =>
    }

    method At(i: nat) returns (t: T) 
      requires Valid()
      requires i < Length()
    {
      var expr := Force();
      return expr.At(i);
    }
  }

  class {:extern} AtomicBox<T> {
    ghost const inv: T -> bool

    constructor(t: T, ghost inv: T -> bool)
      ensures this.inv == inv

    method Put(t: T)
      requires inv(t)

    method Get() returns (t: T)
      ensures inv(t)
  }
}