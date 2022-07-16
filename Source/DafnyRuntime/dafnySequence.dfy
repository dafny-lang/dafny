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
    | Lazy(ghost value: seq<T>, ghost boxSize: nat,
           exprBox: AtomicBox<SeqExpr<T>>, length: nat) 
  {
    ghost predicate Valid()
      decreases Size(), 0
    {
      match this
      case Concat(left, right, length) => 
        && left.Valid()
        && right.Valid()
        && left.Length() + right.Length() == length
      case Lazy(value, size, exprBox, length) => 
        && length == |value|
        && exprBox.inv == ((e: SeqExpr<T>) => 
          && e.Size() < size
          && e.Valid() 
          && e.Value() == value)
      case _ => true
    }

    ghost function Size(): nat {
      match this {
        case Concat(left, right, _) => 1 + left.Size() + right.Size()
        case Lazy(_, boxSize, _, _) => 1 + boxSize
        case _ => 1
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
      decreases Size(), 2
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
      requires builder.Valid()
      requires toAppendAfter.Valid?()
      requires forall e <- toAppendAfter.Repr :: e.Valid()
      requires builder.Remaining() == |Value()| + |ConcatValueOnStack(toAppendAfter.Repr)|
      requires {builder, builder.storage} !! {toAppendAfter, toAppendAfter.data}
      modifies builder, builder.storage, toAppendAfter, toAppendAfter.data
      decreases Size() + SizeSum(toAppendAfter.Repr)
      ensures builder.Valid()
      ensures builder.Value() == old(builder.Value()) + Value() + ConcatValueOnStack(old(toAppendAfter.Repr));
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
            LemmaConcatValueOnStackWithTip(toAppendAfter.Repr, next);
            next.AppendValue(builder, toAppendAfter);
          }
        }
        case Concat(left, right, _) => {
          :- expect toAppendAfter.Push(right);
          LemmaConcatValueOnStackWithTip(old(toAppendAfter.Repr), right);
          assert SizeSum(toAppendAfter.Repr) == old(SizeSum(toAppendAfter.Repr)) + right.Size();
          left.AppendValue(builder, toAppendAfter);
        }
        case Lazy(_, _, exprBox, _) => {
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

  // TODO: Make this an extern. How to monomorphize?
  class SeqBuilder<T> {
    const storage: array<T>
    var size: nat

    ghost predicate Valid() reads this {
      0 <= size <= storage.Length
    }

    constructor(length: nat) 
      ensures Valid()
      ensures Value() == []
      ensures Remaining() == length
      ensures fresh(storage)
    {
      storage := new T[length];
      size := 0;
    }

    ghost function Remaining(): nat
      requires Valid()
      reads this, storage
    {
      storage.Length - size
    }

    method Append(t: seq<T>) 
      requires Valid()
      requires size + |t| <= storage.Length
      modifies this, storage
      ensures Valid()
      ensures Value() == old(Value()) + t
    {
      // TODO: Need an extern for an optimized way to do this
      forall i | 0 <= i < |t| {
        storage[size + i] := t[i];
      }
      size := size + |t|;
    }

    function Value(): seq<T> 
      requires Valid()
      reads this, storage
    {
      storage[..size]
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