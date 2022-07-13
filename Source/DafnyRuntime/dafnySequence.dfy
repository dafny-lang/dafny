
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

  function CalcConcat<T>(left: SeqExpr<T>, right: SeqExpr<T>, length: nat): seq<T> {
    left.Value() + right.Value()
  } by method {
    var builder: SeqBuilder<T> := new SeqBuilder(length);
    var toVisit := new Stack<SeqExpr<T>>(Empty);
    :- expect toVisit.Push(right);
    :- expect toVisit.Push(left);

    while (0 < toVisit.size) 
      invariant toVisit.Valid?()
      invariant fresh(toVisit)
      invariant fresh(toVisit.data)
    {
      // TODO: Have to add Pop() to Stacks.dfy
      var next := toVisit.Pop();

      match next
      case Concat(nextLeft, nextRight, _) => {
        // No way to grab the result of Force() here if present, but that's okay
        :- expect toVisit.Push(nextRight);
        :- expect toVisit.Push(nextLeft);
      }
      case _ => {
        builder.Append(next.Value());
      }
    }
    
    return builder.Value();
  }

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
    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr

    function Value(): seq<T>
      requires Valid()
      reads Repr
      ensures |Value()| == Length()

    function Length(): nat
      requires Valid()
      reads Repr

    function At(i: nat): T
      reads this, Repr
      requires Valid()
      requires i < Length()

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

  class LazySeq<T> extends Seq<T> {
    var expr: SeqExpr<T>

    constructor(expr: SeqExpr<T>) 
      requires expr.Valid()
      ensures Valid()
    {
      this.expr := expr;
      this.Repr := {this};
    }

    ghost predicate Valid() 
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      Repr == {this} && expr.Valid()
    }

    function Value(): seq<T> 
      requires Valid()
      reads Repr
      ensures |Value()| == Length()
    {
      expr.Value()
    }

    function Length(): nat 
      requires Valid()
      reads Repr
    {
      expr.Length()
    }

    method Concatenate(s: Seq<T>) returns (l: Seq<T>) 
      requires Valid() && s.Valid()
      ensures l.Valid()
    {
      var sLength := s.Length();
      if (s as Seq<T>) is LazySeq<T> {
        var lazyS := (s as Seq<T>) as LazySeq<T>;
        l := new LazySeq(Concat(expr, lazyS.expr, expr.Length() + sLength));
      } else {
        l := new LazySeq(Concat(expr, Direct(s.Value()), expr.Length() + sLength));
      }
      
    }

    method Force()
    {
      match expr
      case Concat(left, right, length) => {
        var s := CalcConcat(left, right, length);
        expr := Direct(s);
      }
      case _ =>
    }

    function At(i: nat): T 
      requires Valid()
      requires i < Length()
      reads this, Repr
    {
      assert expr.Valid();
      expr.At(i)
    }
    by method {
      Force();
      return expr.At(i);
    }
  }
}