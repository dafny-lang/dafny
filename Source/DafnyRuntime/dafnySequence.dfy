
include "../../Test/libraries/src/JSON/Stacks.dfy"
include "../../Test/libraries/src/Collections/Sequences/Seq.dfy"
include "../../Test/libraries/src/Math.dfy"

module {:options "/functionSyntax:4"} MetaSeq {

  import Math
  import Seq

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
      match this {
        case Concat(left, right, _) => 1 + Math.Max(left.Depth(), right.Depth())
        case _ => 0
      }
    }

    ghost function NodeCount(): nat {
      match this {
        case Concat(left, right, _) => 1 + left.NodeCount() + right.NodeCount()
        case _ => 1
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
      case Concat(left, right, length) => left.Value() + right.Value()
      case Lazy(value, _, _) => value
    } by method {
      match this
      case Empty => return [];
      case Direct(a) => return a;
      case Concat(left, right, length) => {
        var builder := new SeqBuilder<T>(length);
        AppendValue(builder);
        return builder.Value();
      }
      case Lazy(_, seqExpr, _) => {
        var expr := exprBox.Get();
        var value := expr.Value();
        exprBox.Put(Direct(value));
        return value;
      }
    }

    method AppendValue(builder: SeqBuilder<T>) 
      requires Valid()
      modifies builder
      ensures builder.Value() == old(builder.Value()) + Value();
    {
      match this {
        case Empty =>
        case Direct(a) => {
          builder.Append(a);
        }
        case Concat(left, right, _) => {
          left.AppendValue(builder);
          right.AppendValue(builder);
        }
        case Lazy(value, _, _) => {
          var expr := exprBox.Get();
          expr.AppendValue(builder);
        }
      }
    }
  }

  // function CalcConcatStackBased<T>(left: SeqExpr<T>, right: SeqExpr<T>, length: nat): (result: seq<T>)
  //   requires left.Valid()
  //   requires right.Valid()
  //   requires left.Length() + right.Length() == length
  //   decreases 1 + Math.Max(left.Depth(), right.Depth())
  // {
  //   left.Value() + right.Value()
  // } by method {
  //   var builder: SeqBuilder<T> := new SeqBuilder(length);
  //   assert builder.Value() == [];

  //   var toVisit := new Stack<SeqExpr<T>>(Empty);
  //   :- expect toVisit.Push(right);
  //   :- expect toVisit.Push(left);
  //   assert forall e <- toVisit.Repr :: e.Valid() && e.Depth() < 1 + Math.Max(left.Depth(), right.Depth());
    
  //   ghost var answer := left.Value() + right.Value();
  //   assert toVisit.Repr == [right, left];
  //   var reversed := Seq.Reverse(toVisit.Repr);
  //   assert reversed == [left, right];
  //   assert forall e <- reversed :: e.Valid() && e.Depth() < 1 + Math.Max(left.Depth(), right.Depth());
  //   ghost var valueFn := (e: SeqExpr<T>) requires e.Valid() => e.Value();
  //   calc {
  //     builder.Value() + Seq.Flatten(Seq.Map(valueFn, Seq.Reverse(toVisit.Repr)));
  //     [] + Seq.Flatten(Seq.Map(valueFn, Seq.Reverse(toVisit.Repr)));
  //     Seq.Flatten(Seq.Map(valueFn, Seq.Reverse(toVisit.Repr)));
  //     Seq.Flatten(Seq.Map(valueFn, [left, right]));
  //     { reveal Seq.Map(); }
  //     Seq.Flatten([left.Value()] + Seq.Map(valueFn, [right]));
  //     { reveal Seq.Map(); }
  //     Seq.Flatten([left.Value(), right.Value()] + []);
  //     left.Value() + Seq.Flatten([right.Value()]);
  //     left.Value() + right.Value();
  //     answer;
  //   }
  //   assert builder.Value() + Seq.Flatten(Seq.Map((e: SeqExpr<T>) requires e.Valid() => e.Value(), Seq.Reverse(toVisit.Repr))) == answer;

  //   while 0 < toVisit.size
  //     invariant toVisit.Valid?()
  //     invariant fresh(toVisit.data)
  //     invariant forall e <- toVisit.Repr :: e.Valid() && e.Depth() < 1 + Math.Max(left.Depth(), right.Depth())
  //     invariant builder.Value() + ConcatValueOnStack(toVisit.Repr) == answer
  //     decreases TotalNodesOnStack(toVisit.Repr) + TotalDepthOnStack(toVisit.Repr)
  //   {
  //     ghost var stackBefore := toVisit.Repr;
  //     ghost var builderBefore := builder.Value();
  //     ghost var stackNodesBefore := TotalNodesOnStack(toVisit.Repr);
  //     ghost var stackDepthBefore :=  TotalDepthOnStack(toVisit.Repr);

  //     // TODO: Have to add Pop() to Stacks.dfy
  //     var next := toVisit.Pop();
  //     assert next.Valid();

  //     match next {
  //       case Concat(nextLeft, nextRight, _) =>
  //         :- expect toVisit.Push(nextRight);
  //         :- expect toVisit.Push(nextLeft);
  //       case _ =>
  //         assert next.Depth() == 0;
  //         builder.Append(next.Value());
  //         assert toVisit.Repr + [next] == stackBefore;
  //         SumDistributesOverConcat(toVisit.Repr, [next]);
  //         assert TotalNodesOnStack(toVisit.Repr) + next.NodeCount() == TotalNodesOnStack(stackBefore);
  //         assert stackNodesBefore < TotalNodesOnStack(toVisit.Repr);
  //     }
  //   }
    
  //   assert |toVisit.Repr| == 0;
  //   return builder.Value();
  // }

  // ghost function ConcatValueOnStack<T>(s: seq<SeqExpr<T>>): seq<T>
  //   requires (forall e <- s :: e.Valid())
  // {
  //   var valueFn := (e: SeqExpr<T>) requires e.Valid() => e.Value();
  //   Seq.Flatten(Seq.Map(valueFn, Seq.Reverse(s)))
  // }

  // ghost function TotalDepthOnStack<T>(s: seq<SeqExpr<T>>): nat
  // {
  //   Sum(Seq.Map((e: SeqExpr<T>) => e.Depth(), s))
  // }

  // ghost function TotalNodesOnStack<T>(s: seq<SeqExpr<T>>): nat
  // {
  //   Sum(Seq.Map((e: SeqExpr<T>) => e.NodeCount(), s))
  // }

  // lemma 

  // function Sum(s: seq<nat>): nat {
  //   Seq.FoldLeft((x, y) => x + y, 0, s)
  // }

  // lemma SumDistributesOverConcat(a: seq<nat>, b: seq<nat>)
  //   ensures Sum(a + b) == Sum(a) + Sum(b)
  // {
  //   var f := (x, y) => x + y;
  //   calc {
  //     Sum(a + b);
  //     Seq.FoldLeft(f, 0, a + b);
  //     { Seq.LemmaFoldLeftDistributesOverConcat(f, 0, a, b); }
  //     Seq.FoldLeft(f, Seq.FoldLeft(f, 0, a), b);
  //     Sum(a) + Sum(b);
  //   }
  // }

  // TODO: Make this an extern. How to monomorphize?
  class SeqBuilder<T> {
    var value: seq<T>

    constructor(length: nat) 
      ensures Value() == []
    {
      value := [];
    }

    method Append(t: seq<T>) 
      modifies this
      ensures Value() == old(Value()) + t
    {
      value := value + t;
    }

    function Value(): seq<T> reads this {
      value
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

    constructor(ghost inv: T -> bool, t: T)
      requires inv(t)
      ensures this.inv == inv

    method Put(t: T)
      requires inv(t)

    method Get() returns (t: T)
      ensures inv(t)
  }
}