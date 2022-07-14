
include "../../Test/libraries/src/JSON/Stacks.dfy"
include "../../Test/libraries/src/Collections/Sequences/Seq.dfy"
include "../../Test/libraries/src/Math.dfy"

module {:options "/functionSyntax:4"} MetaSeq {

  import Math

  import opened Stacks

  datatype SeqExpr<T> = 
    | Empty
    | Direct(a: seq<T>)
    | Concat(left: SeqExpr<T>, right: SeqExpr<T>, length: nat)
    | Lazy(ghost value: seq<T>, exprBox: AtomicBox<SeqExpr<T>>, length: nat) 
  {
    ghost predicate Valid()
      decreases Depth(), 0
    {
      match this
      case Concat(left, right, length) => 
        && left.Valid()
        && right.Valid()
        && left.Length() + right.Length() == length
      case Lazy(value, exprBox, length) => 
        && length == |value|
        && exprBox.inv == ((e: SeqExpr<T>) => e.Valid() && e.Value() == value)
      case _ => true
    }

    ghost function Depth(): nat {
      1 + match this {
        case Empty => 0
        case Direct(_) => 0
        case Concat(left, right, _) => Math.Max(left.Depth(), right.Depth())
        case Lazy(_, _, _) => 0
      }
    }

    function Length(): nat {
      match this
      case Empty => 0
      case Direct(a) => |a|
      case Concat(_, _, length) => length
      case Lazy(_, _, length) => length
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
      decreases Depth(), 2
      ensures |Value()| == Length()
    {
      match this
      case Empty => []
      case Direct(a) => a
      case Concat(_, _, _) => CalcConcat(this)
      case Lazy(value, _, _) => value
    } by method {
      match this
      case Empty => return [];
      case Direct(a) => return a;
      case Concat(_, _, _) => return CalcConcat(this);
      case Lazy(_, seqExpr, _) => {
        var expr := exprBox.Get();
        var value := expr.Value();
        exprBox.Put(Direct(value));
        return value;
      }
    }
  }

  function CalcConcat<T>(expr: SeqExpr<T>): (result: seq<T>)
    requires expr.Valid()
    decreases expr.Depth(), 1
  {
    expr.Value()
  } by method {
    var builder: SeqBuilder<T> := new SeqBuilder(expr.Length());
    var toVisit := new Stack<SeqExpr<T>>(Empty);
    :- expect toVisit.Push(expr);

    ghost var n: nat := expr.Length();
    while 0 < toVisit.size
      invariant toVisit.Valid?()
      invariant fresh(toVisit)
      invariant fresh(toVisit.data)
      invariant forall e <- toVisit.Repr :: e.Valid()
      decreases n
    {
      // TODO: Have to add Pop() to Stacks.dfy
      var next := toVisit.Pop();

      match next {
        case Concat(nextLeft, nextRight, _) =>
          :- expect toVisit.Push(nextRight);
          :- expect toVisit.Push(nextLeft);
        case _ =>
          builder.Append(next.Value());
      }

      Assume(n > 0);
      n := n - 1;
    }
    
    var v := builder.Value();
    Assume(v == expr.Value());
    return v;
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

  // trait {:termination false} Validatable {
  //   // Ghost state tracking the common set of objects most
  //   // methods need to read.
  //   ghost var Repr: set<object>

  //   ghost predicate Valid()
  //     reads this, Repr
  //     ensures Valid() ==> this in Repr

  //   // Convenience predicate for when your object's validity depends on one
  //   // or more other objects.
  //   ghost predicate ValidComponent(component: Validatable)
  //     reads this, Repr 
  //   {
  //     && component in Repr
  //     && component.Repr <= Repr
  //     && this !in component.Repr
  //     && component.Valid()
  //   }

  //   // Convenience predicate, since you often want to assert that 
  //   // new objects in Repr are fresh as well in most postconditions.
  //   twostate predicate ValidAndDisjoint()
  //     reads this, Repr
  //   {
  //     Valid() && fresh(Repr - old(Repr))
  //   }
  // }

  // // TODO: I THINK this can be a SeqExpr too...
  // class LazySeq<T> extends Seq<T> {
  //   const length: nat
  //   const exprBox: AtomicBox<SeqExpr<T>>
    
  //   constructor(expr: SeqExpr<T>) 
  //     requires expr.Valid()
  //     ensures Valid()
  //     ensures this.value == expr.Value()
  //   {
  //     this.length := expr.Length();
  //     this.exprBox := new AtomicBox(expr, ((e: SeqExpr<T>) => e.Valid() && e.Value() == expr.Value()));

  //     this.Repr := {this};
  //     this.value := expr.Value();
  //   }

  //   ghost predicate Valid() 
  //     reads this, Repr
  //     ensures Valid() ==> this in Repr
  //   {
  //     && Repr == {this}
  //     && length == |value|
  //     && exprBox.inv == ((e: SeqExpr<T>) => e.Valid() && e.Value() == value)
  //   }

  //   method Value() returns (s: seq<T>)
  //     requires Valid()
  //     ensures s == value
  //   {
  //     var expr := Force();
  //     return expr.Value();
  //   }

  //   function Length(): nat 
  //     requires Valid()
  //     reads Repr
  //   {
  //     length
  //   }

  //   method Concatenate(rhs: Seq<T>) returns (l: Seq<T>) 
  //     requires Valid() && rhs.Valid()
  //     ensures l.Valid()
  //   {
  //     var expr := exprBox.Get();
  //     var rhsExpr: SeqExpr<T>;
  //     if (rhs as Seq<T>) is LazySeq<T> {
  //       var lazyS := (rhs as Seq<T>) as LazySeq<T>;
  //       rhsExpr := lazyS.exprBox.Get();
  //     } else {
  //       var rhsValue := rhs.Value();
  //       rhsExpr := Direct(rhsValue);
  //     }
  //     var sLength := rhsExpr.Length();
  //     l := new LazySeq(Concat(expr, rhsExpr, expr.Length() + sLength));
  //   }

  //   method At(i: nat) returns (t: T) 
  //     requires Valid()
  //     requires i < Length()
  //   {
  //     var expr := Force();
  //     return expr.At(i);
  //   }
  // }

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