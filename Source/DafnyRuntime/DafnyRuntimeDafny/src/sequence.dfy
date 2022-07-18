include "../../../../Test/libraries/src/Collections/Sequences/Seq.dfy"
include "../../../../Test/libraries/src/Math.dfy"

include "array.dfy"
include "frames.dfy"

module {:options "/functionSyntax:4"} MetaSeq {

  import Math
  import Seq

  import opened Frames
  import opened Arrays

  // TODO: static analysis to assert that all methods that are called directly from Dafny syntax
  // (e.g. s[i] -> s.Select(i)) have `modifies {}` (implicitly or explicitly).
  // TODO: Would also be good to assert that seq<T> is only used in specifications.
  // TODO: Align terminology between length/size/etc.
  // TODO: How to deal
  trait SeqExpr<T> extends Validatable {
   
    ghost predicate Valid()
      reads this, Repr
      decreases Repr, 0
      ensures Valid() ==> this in Repr
    
    ghost function Size(): nat
      requires Valid()
      reads this, Repr
      decreases Repr, 1

    function Length(): nat 
      requires Valid() 
      reads Repr
      decreases Repr, 1

    function Depth(): nat

    ghost function Value(): seq<T> 
      requires Valid()
      reads this, Repr
      decreases Repr, 2
      ensures |Value()| == Length()

    method ToArray() returns (ret: InitializedArray<T>)
      requires Valid()
      decreases Size(), 2
      ensures ret.Valid()
      ensures ret.Value() == Value()

    method Concatenate(s: SeqExpr<T>) returns (ret: SeqExpr<T>)
      requires Valid()
      requires s.Valid()
      ensures ret.Valid()
    {
      var c := new Concat(this, s);
      ret := new Lazy(c);
    }
  }

  class Direct<T> extends SeqExpr<T> {
    const value: InitializedArray<T>

    ghost predicate Valid()
      reads this, Repr
      decreases Repr, 0
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && ValidComponent(value.a)
      && value.Valid()
    }

    constructor(value: InitializedArray<T>) 
      requires value.Valid()
      ensures Valid()
      ensures fresh(Repr - value.a.Repr)
    {
      this.value := value;

      Repr := {this} + value.a.Repr;
    }

    ghost function Size(): nat 
      requires Valid()
      reads this, Repr
      decreases Repr, 1
    {
      1
    }

    function Depth(): nat {
      1
    }

    function Length(): nat 
      requires Valid() 
      reads Repr 
      decreases Repr, 1
    {
      value.a.Length()
    }

    ghost function Value(): seq<T> 
      requires Valid()
      reads this, Repr
      decreases Repr, 2
      ensures |Value()| == Length()
    {
      value.Value()
    }

    method ToArray() returns (ret: InitializedArray<T>)
      requires Valid()
      decreases Size(), 2
      ensures ret.Valid()
      ensures ret.Value() == Value()
    {
      return value;
    }
  }

  class Concat<T> extends SeqExpr<T> {
    const left: SeqExpr<T>
    const right: SeqExpr<T>
    const length: nat
    const depth: nat

    ghost predicate Valid() 
      reads this, Repr
      decreases Repr, 0
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && ValidComponent(left)
      && ValidComponent(right)
      && length == left.Length() + right.Length()
      && depth == 1 + Math.Max(left.Depth(), right.Depth())
    }

    constructor(left: SeqExpr<T>, right: SeqExpr<T>) 
      requires left.Valid()
      requires right.Valid()
      ensures Valid()
      ensures fresh(Repr - left.Repr - right.Repr)
    {
      this.left := left;
      this.right := right;
      this.length := left.Length() + right.Length();
      this.depth := 1 + Math.Max(left.Depth(), right.Depth());

      Repr := {this} + left.Repr + right.Repr;
    }

    ghost function Size(): nat
      requires Valid()
      reads this, Repr
      decreases Repr, 1
    {
      1 + left.Size() + right.Size()
    }

    function Depth(): nat {
      depth
    }

    function Length(): nat 
      requires Valid() 
      reads Repr 
      decreases Repr, 1
    {
      length
    }

    ghost function Value(): seq<T> 
      requires Valid()
      reads this, Repr
      decreases Repr, 2
      ensures |Value()| == Length()
    {
      var result := left.Value() + right.Value();
      assert |result| == length;
      assert length == Length();
      result
    }

    method ToArray() returns (ret: InitializedArray<T>)
      requires Valid()
      decreases Size(), 2
      ensures ret.Valid()
      ensures ret.Value() == Value()
    {
      var builder := new ResizableArray<T>(length);
      var toAppendAfter := new ResizableArray<SeqExpr<T>>(depth);
      AppendValue(builder, toAppendAfter);
      return InitializedArray(builder.storage);
    }

    method {:tailrecursion} AppendValue(builder: ResizableArray<T>, toAppendAfter: ResizableArray<SeqExpr<T>>)
      requires Valid()
      requires builder.Valid()
      requires toAppendAfter.Valid()
      requires forall e <- toAppendAfter.Value() :: e.Valid()
      requires builder.Remaining() == |Value()| + |ConcatValueOnStack(toAppendAfter.Value())|
      requires builder.Repr !! toAppendAfter.Repr
      modifies builder.Repr, toAppendAfter.Repr
      decreases Size() + SizeSum(toAppendAfter.Value())
      ensures builder.Valid()
      ensures builder.Value() == old(builder.Value()) + Value() + ConcatValueOnStack(old(toAppendAfter.Value()));
    {
      // TODO: Optimized version
      // match this {
      //   case Direct(a) => {
      //     builder.Append(a);
      //     if 0 < toAppendAfter.size {
      //       var next := toAppendAfter.RemoveLast();
      //       LemmaConcatValueOnStackWithTip(toAppendAfter.Value(), next);
      //       next.AppendValue(builder, toAppendAfter);
      //     }
      //   }
      //   case ConcatBoth(left, right, _, _) => {
      //     toAppendAfter.AddLast(right);
      //     LemmaConcatValueOnStackWithTip(old(toAppendAfter.Value()), right);
      //     assert SizeSum(toAppendAfter.Value()) == old(SizeSum(toAppendAfter.Value())) + right.Size();
      //     left.AppendValue(builder, toAppendAfter);
      //   }
      //   case Lazy(_, _, exprBox, _, _) => {
      //     var expr := exprBox.Get();
      //     expr.AppendValue(builder, toAppendAfter);
      //   }
      // }
    }
  }

  class Lazy<T> extends SeqExpr<T> {
    ghost const value: seq<T>
    ghost const size: nat
    const exprBox: AtomicBox<SeqExpr<T>>
    const length: nat
    const depth: nat

    ghost predicate Valid() 
      reads this, Repr
      decreases Repr, 0
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && length == |value|
      && exprBox.inv == ((e: SeqExpr<T>) reads e => 
        && e.Size() < size
        && e.Depth() < depth
        && e.Valid() 
        && e.Value() == value)
    }

    constructor(wrapped: SeqExpr<T>) 
      requires wrapped.Valid()
      ensures Valid()
      ensures fresh(Repr)
    {
      var depth := 1 + wrapped.Depth();
      var value := wrapped.Value();
      var size := 1 + wrapped.Size();
      ghost var inv := ((e: SeqExpr<T>) => 
          && e.Size() < size
          && e.Depth() < depth
          && e.Valid() 
          && e.Value() == value);
      this.exprBox := new AtomicBox(inv, wrapped);

      this.depth := depth;
      this.value := value;
      this.size := size;
    }

    ghost function Size(): nat 
      requires Valid()
      reads this, Repr
      decreases Repr, 1
    {
      size
    }

    function Depth(): nat {
      depth
    }

    function Length(): nat 
      requires Valid() 
      reads Repr
      decreases Repr, 1
    {
      length
    }
    
    ghost function Value(): seq<T> 
      requires Valid()
      reads this, Repr
      decreases Repr, 2
      ensures |Value()| == Length()
    {
      assert |value| == Length();
      value
    }

    method ToArray() returns (ret: InitializedArray<T>)
      requires Valid()
      decreases Size(), 2
      ensures ret.Valid()
      ensures ret.Value() == Value()
    {
      var expr := exprBox.Get();
      var a := expr.ToArray();
      var direct := new Direct(a);
      exprBox.Put(direct);
      return a;
    }
  }

  ghost function ConcatValueOnStack<T>(s: seq<SeqExpr<T>>): seq<T>
    reads (set e <- s, o <- e.Repr :: o)
    requires (forall e <- s :: e.Valid())
  {
    var valueFn := (e: SeqExpr<T>) requires e.Valid() reads e, e.Repr => e.Value();
    Seq.Flatten(Seq.Map(valueFn, Seq.Reverse(s)))
  }

  lemma LemmaConcatValueOnStackWithTip<T>(s: seq<SeqExpr<T>>, x: SeqExpr<T>) 
    requires (forall e <- s :: e.Valid())
    requires x.Valid()
    ensures ConcatValueOnStack(s + [x]) == x.Value() + ConcatValueOnStack(s)
  {
    var valueFn := (e: SeqExpr<T>) reads e, e.Repr requires e.Valid() => e.Value();
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

  ghost function SizeSum<T>(s: seq<SeqExpr<T>>): nat 
    reads set e <- s, o <- e.Repr :: o
    requires forall e <- s :: e.Valid()
  {
    if |s| == 0 then 
      0 
    else
      var last := |s| - 1;
      SizeSum(s[..last]) + s[last].Size()
  }

  class ResizableArray<T> extends Validatable {
    const storage: Array<T>
    var size: nat

    ghost predicate Valid() reads this, Repr 
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && ValidComponent(storage)
      && 0 <= size <= storage.Length()
      && forall i | 0 <= i < size :: storage.values[i].Set?
    }

    constructor(length: nat) 
      ensures Valid()
      ensures Value() == []
      ensures Remaining() == length
      ensures fresh(Repr)
    {
      storage := new DafnyArray<T>(length);
      size := 0;
      new;
      Repr := {this} + storage.Repr;
    }

    ghost function Value(): seq<T>
      requires Valid()
      reads this, Repr
    {
      seq(size, i requires 0 <= i < size && Valid() reads this, Repr => storage.Read(i))
    }

    ghost function Remaining(): nat
      requires Valid()
      reads this, Repr
    {
      storage.Length() - size
    }

    method AddLast(t: T) 
      requires Valid()
      requires size + 1 <= storage.Length()
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Value() == old(Value()) + [t]
      ensures Remaining() == old(Remaining()) - 1
    {
      storage.Write(size, t);
      size := size + 1;
    }

    method RemoveLast() returns (t: T) 
      requires Valid()
      requires 0 < size
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Value() == old(Value())[..size]
      ensures Remaining() == old(Remaining()) + 1
    {
      t := storage.Read(size - 1);
      size := size - 1;
    }

    method Append(other: InitializedArray<T>) 
      requires Valid()
      requires other.Valid()
      requires size + other.a.Length() <= storage.Length()
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Value() == old(Value()) + other.Value()
      ensures Remaining() == old(Remaining()) - other.a.Length()
    {
      storage.WriteRangeArray(size, other.a, 0, other.a.Length());
      size := size + other.a.Length();
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