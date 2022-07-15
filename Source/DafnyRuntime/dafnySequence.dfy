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
    | Lazy(ghost value: seq<T>, ghost boxDepth: nat, exprBox: AtomicBox<SeqExpr<T>>, length: nat) 
  {
    ghost predicate Valid()
      decreases Depth(), 0
    {
      match this
      case Concat(left, right, length) => 
        && left.Valid()
        && right.Valid()
        && left.Length() + right.Length() == length
      case Lazy(value, depth, exprBox, length) => 
        && length == |value|
        && exprBox.inv == ((e: SeqExpr<T>) => e.Depth() < depth && e.Valid() && e.Value() == value)
      case _ => true
    }

    ghost function Depth(): nat {
      match this {
        case Concat(left, right, _) => 1 + Math.Max(left.Depth(), right.Depth())
        case Lazy(_, depth, _, _) => depth
        case _ => 0
      }
    }

    function Length(): nat {
      match this
      case Empty => 0
      case Direct(a) => |a|
      case Concat(_, _, length) => length
      case Lazy(_, _, _, length) => length
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
      case Lazy(value, _, _, _) => value
    } by method {
      match this
      case Empty => return [];
      case Direct(a) => return a;
      case Concat(left, right, length) => {
        var builder := new SeqBuilder<T>(length);
        var toAppendAfter := new Stack<SeqExpr<T>>(Empty);
        AppendValue(builder, toAppendAfter);
        return builder.Value();
      }
      case Lazy(_, _, seqExpr, _) => {
        var expr := exprBox.Get();
        var value := expr.Value();
        exprBox.Put(Direct(value));
        return value;
      }
    }

    method {:tailrecursion} AppendValue(builder: SeqBuilder<T>, toAppendAfter: Stack<SeqExpr<T>>) 
      requires Valid()
      requires toAppendAfter.Valid?()
      requires forall e <- toAppendAfter.Repr :: e.Valid()
      modifies builder, toAppendAfter, toAppendAfter.data
      decreases toAppendAfter.size, Depth()
      ensures builder.Value() == old(builder.Value()) + Value() + ConcatValueOnStack(toAppendAfter.Repr);
    {
      match this {
        case Empty =>
          if 0 < toAppendAfter.size {
            var next := toAppendAfter.Pop();
            LemmaConcatValueOnStackWithTip(toAppendAfter.Repr, next);
            next.AppendValue(builder, toAppendAfter);
          }
        case Direct(a) => {
          builder.Append(a);
          if 0 < toAppendAfter.size {
            var next := toAppendAfter.Pop();
            next.AppendValue(builder, toAppendAfter);
          }
        }
        case Concat(left, right, _) => {
          :- expect toAppendAfter.Push(right);
          LemmaConcatValueOnStackWithTip(old(toAppendAfter.Repr), right);
          left.AppendValue(builder, toAppendAfter);
        }
        case Lazy(value, _, _, _) => {
          var expr := exprBox.Get();
          expr.AppendValue(builder, toAppendAfter);
        }
      }
    }
  }

  ghost function ConcatValueOnStack<T>(s: seq<SeqExpr<T>>): seq<T>
    requires (forall e <- s :: e.Valid())
  {
    var valueFn := (e: SeqExpr<T>) requires e.Valid() => e.Value();
    Seq.Flatten(Seq.Map(valueFn, Seq.Reverse(s)))
  }

  lemma LemmaConcatValueOnStackWithTip<T>(s: seq<SeqExpr<T>>, x: SeqExpr<T>) 
    requires (forall e <- s :: e.Valid())
    requires x.Valid()
    ensures ConcatValueOnStack(s + [x]) == ConcatValueOnStack(s) + x.Value()
  {
    reveal Seq.Map();
  }

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