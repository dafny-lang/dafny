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
    | Lazy(ghost value: seq<T>, ghost boxDepth: nat, ghost boxSize: nat,
           exprBox: AtomicBox<SeqExpr<T>>, length: nat) 
  {
    ghost predicate Valid()
      decreases Depth(), 0
    {
      match this
      case Concat(left, right, length) => 
        && left.Valid()
        && right.Valid()
        && left.Length() + right.Length() == length
      case Lazy(value, depth, size, exprBox, length) => 
        && length == |value|
        && exprBox.inv == ((e: SeqExpr<T>) => 
          && e.Depth() < depth 
          && e.Size() < size
          && e.Valid() 
          && e.Value() == value)
      case _ => true
    }

    ghost function Depth(): nat {
      match this {
        case Concat(left, right, _) => 1 + Math.Max(left.Depth(), right.Depth())
        case Lazy(_, depth, _, _, _) => depth
        case _ => 0
      }
    }

    ghost function Size(): nat {
      match this {
        case Concat(left, right, _) => 1 + left.Size() + right.Size()
        case Lazy(_, _, boxSize, _, _) => 1 + boxSize
        case _ => 1
      }
    }

    function Length(): nat {
      match this
      case Empty => 0
      case Direct(a) => |a|
      case Concat(_, _, length) => length
      case Lazy(_, _, _, _, length) => length
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
      case Lazy(value, _, _, _, _) => value
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
      case Lazy(_, _, _, seqExpr, _) => {
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
      requires {builder} !! {toAppendAfter, toAppendAfter.data}
      modifies builder, toAppendAfter, toAppendAfter.data
      decreases Size() + SizeSum(toAppendAfter.Repr)
      ensures builder.Value() == old(builder.Value()) + Value() + ConcatValueOnStack(old(toAppendAfter.Repr));
    {
      match this {
        case Empty =>
          builder.Append([]);
          if 0 < toAppendAfter.size {
            var next := toAppendAfter.Pop();
            assert toAppendAfter.Repr + [next] == old(toAppendAfter.Repr);
            LemmaConcatValueOnStackWithTip(toAppendAfter.Repr, next);
            assert next.Value() + ConcatValueOnStack(toAppendAfter.Repr) == ConcatValueOnStack(old(toAppendAfter.Repr));
            next.AppendValue(builder, toAppendAfter);
            assert builder.Value() == (old(builder.Value()) + Value()) + ConcatValueOnStack(old(toAppendAfter.Repr));
          }
        case Direct(a) => {
          builder.Append(a);
          if 0 < toAppendAfter.size {
            var next := toAppendAfter.Pop();
            assert toAppendAfter.Repr + [next] == old(toAppendAfter.Repr);
            LemmaConcatValueOnStackWithTip(toAppendAfter.Repr, next);
            assert next.Value() + ConcatValueOnStack(toAppendAfter.Repr) == ConcatValueOnStack(old(toAppendAfter.Repr));
            next.AppendValue(builder, toAppendAfter);
            assert builder.Value() == (old(builder.Value()) + Value()) + ConcatValueOnStack(old(toAppendAfter.Repr));
          }
        }
        case Concat(left, right, _) => {
          :- expect toAppendAfter.Push(right);
          LemmaConcatValueOnStackWithTip(old(toAppendAfter.Repr), right);
          assert SizeSum(toAppendAfter.Repr) == old(SizeSum(toAppendAfter.Repr)) + right.Size();
          left.AppendValue(builder, toAppendAfter);
        }
        case Lazy(_, _, _, exprBox, _) => {
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
    ensures ConcatValueOnStack(s + [x]) == x.Value() + ConcatValueOnStack(s)
    ensures SizeSum(s + [x]) == x.Size() + SizeSum(s)
  {
    var valueFn := (e: SeqExpr<T>) requires e.Valid() => e.Value();
    calc {
      ConcatValueOnStack(s + [x]);
      Seq.Flatten(Seq.Map(valueFn, Seq.Reverse(s + [x])));
      { reveal Seq.Reverse(); }
      Seq.Flatten(Seq.Map(valueFn, [x] + Seq.Reverse(s)));
      { reveal Seq.Map(); }
      Seq.Flatten([x.Value()] + Seq.Map(valueFn, Seq.Reverse(s)));
      x.Value() + Seq.Flatten(Seq.Map(valueFn, Seq.Reverse(s)));
      x.Value() + ConcatValueOnStack(s);
    }
  }

  ghost function SizeSum<T>(s: seq<SeqExpr<T>>): nat {
    if |s| == 0 then 
      0 
    else
      var last := |s| - 1;
      SizeSum(s[..last]) + s[last].Size()
  }

  // TODO: Add precondition on allocated length
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