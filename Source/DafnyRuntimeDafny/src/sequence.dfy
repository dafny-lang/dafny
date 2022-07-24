include "array.dfy"
include "atomicBox.dfy"
include "frames.dfy"

module {:options "/functionSyntax:4"} Sequences {

  import opened Frames
  import opened Arrays
  import opened AtomicBoxes

  // TODO: static analysis to assert that all methods that are called directly from Dafny syntax
  // (e.g. s[i] -> s.Select(i)) have `modifies {}` (implicitly or explicitly).
  // TODO: Would also be good to assert that seq<T> is only used in specifications.
  // TODO: Align terminology between length/size/etc.
  trait {:extern} Sequence<+T> {
   
    ghost const size: nat

    ghost predicate Valid()
      decreases size, 0
      ensures Valid() ==> 0 < size
    
    function Length(): nat 
      requires Valid() 
      decreases size, 1

    ghost function Value(): seq<T> 
      requires Valid()
      decreases size, 2
      ensures |Value()| == Length()

    method Select(index: nat) returns (ret: T)
      requires Valid()
      requires index < Length()
      ensures ret == Value()[index]
    {
      var a := ToArray();
      return a.At(index);
    }

    method Drop(lo: nat) returns (ret: Sequence<T>)
      requires Valid()
      requires lo <= Length()
      decreases size, 2
      ensures ret.Valid()
      ensures ret.Value() == Value()[lo..]
    {
      ret := Subsequence(lo, Length());
    }

    method Take(hi: nat) returns (ret: Sequence<T>)
      requires Valid()
      requires hi <= Length()
      decreases size, 2
      ensures ret.Valid()
      ensures ret.Value() == Value()[..hi]
    {
      ret := Subsequence(0, hi);
    }

    method Subsequence(lo: nat, hi: nat) returns (ret: Sequence<T>)
      requires Valid()
      requires lo <= hi <= Length()
      decreases size, 2
      ensures ret.Valid()
      ensures ret.Value() == Value()[lo..hi]
    {
      // Probably not worth pushing this into a ToArray(lo, hi) overload
      // to optimize further, because one x[lo..hi] call is very likely
      // to be followed by several others anyway.
      var a := ToArray();
      var subarray := a.Subarray(lo, hi);
      ret := new ArraySequence(subarray);
    }

    method ToArray() returns (ret: ImmutableArray<T>)
      requires Valid()
      decreases size, 2
      ensures ret.Valid()
      ensures ret.Length() == Length()
      ensures ret.values == Value()
  }

  // TODO: this would be safe(r) if we used a datatype instead, but still not guaranteed.
  // Is there a decent solution in every target language?
  lemma {:axiom} SequenceTypeIsClosed<T>(e: Sequence<T>) 
    ensures
      || e is ArraySequence<T>
      || e is ConcatSequence<T>
      || e is LazySequence<T>

  method Concatenate<T>(left: Sequence<T>, right: Sequence<T>) returns (ret: Sequence<T>)
    requires left.Valid()
    requires right.Valid()
    ensures ret.Valid()
  {
    var c := new ConcatSequence(left, right);
    ret := new LazySequence(c);
  }

  class ArraySequence<T> extends Sequence<T> {
    const value: ImmutableArray<T>

    ghost predicate Valid()
      decreases size, 0
      ensures Valid() ==> 0 < size
    {
      && value.Valid()
      && size == 1
    }

    constructor(value: ImmutableArray<T>) 
      requires value.Valid()
      ensures Valid()
      ensures this.value == value
    {
      this.value := value;
      this.size := 1;
    }

    function Length(): nat 
      requires Valid() 
      decreases size, 1
    {
      value.Length()
    }

    ghost function Value(): seq<T> 
      requires Valid()
      decreases size, 2
      ensures |Value()| == Length()
    {
      value.values
    }

    method ToArray() returns (ret: ImmutableArray<T>)
      requires Valid()
      decreases size, 2
      ensures ret.Valid()
      ensures ret.Length() == Length()
      ensures ret.values == Value()
    {
      return value;
    }
  }

  class ConcatSequence<T> extends Sequence<T> {
    const left: Sequence<T>
    const right: Sequence<T>
    const length: nat

    ghost predicate Valid() 
      decreases size, 0
      ensures Valid() ==> 0 < size
    {
      && size == 1 + left.size + right.size
      && left.Valid()
      && right.Valid()
      && length == left.Length() + right.Length()
    }

    constructor(left: Sequence<T>, right: Sequence<T>) 
      requires left.Valid()
      requires right.Valid()
      ensures Valid()
    {
      this.left := left;
      this.right := right;
      this.length := left.Length() + right.Length();
      this.size := 1 + left.size + right.size;
    }

    function Length(): nat 
      requires Valid() 
      decreases size, 1
    {
      length
    }

    ghost function Value(): seq<T> 
      requires Valid()
      decreases size, 2
      ensures |Value()| == Length()
    {
      var ret := left.Value() + right.Value();
      assert |ret| == Length();
      ret
    }

    method ToArray() returns (ret: ImmutableArray<T>)
      requires Valid()
      decreases size, 2
      ensures ret.Valid()
      ensures ret.Length() == Length()
      ensures ret.values == Value()
    {
      var builder := new Vector<T>(length);
      var stack := new Vector<Sequence<T>>(10);
      AppendOptimized(builder, this, stack);
      ret := builder.Freeze();
    }
  }

  // Simpler reference implementation of AppendOptimized
  method AppendRecursive<T>(builder: Vector<T>, e: Sequence<T>)
    requires e.Valid()
    requires builder.Valid()
    modifies builder.Repr
    decreases e.size
    ensures builder.ValidAndDisjoint()
    ensures e.Valid()
    ensures builder.Value() == old(builder.Value()) + e.Value();
  {
    if e is ConcatSequence<T> {
      var concat := e as ConcatSequence<T>;
      AppendRecursive(builder, concat.left);
      AppendRecursive(builder, concat.right);
    } else if e is LazySequence<T> {
      var lazy := e as LazySequence<T>;
      var boxed := lazy.box.Get();
      AppendRecursive(builder, boxed);
    } else {
      var a: ImmutableArray<T> := e.ToArray();
      builder.Append(a);
    }
  }

  method {:tailrecursion} AppendOptimized<T>(builder: Vector<T>, e: Sequence<T>, stack: Vector<Sequence<T>>)
    requires e.Valid()
    requires builder.Valid()
    requires stack.Valid()
    requires builder.Repr !! stack.Repr;
    requires forall expr <- stack.Value() :: expr.Valid()
    modifies builder.Repr, stack.Repr
    decreases e.size + SizeSum(stack.Value())
    ensures builder.Valid()
    ensures stack.Valid()
    ensures builder.Value() == old(builder.Value()) + e.Value() + ConcatValueOnStack(old(stack.Value()));
  {
    if e is ConcatSequence<T> {
      var concat := e as ConcatSequence<T>;
      stack.AddLast(concat.right);
      AppendOptimized(builder, concat.left, stack);
    } else if e is LazySequence<T> {
      var lazy := e as LazySequence<T>;
      var boxed := lazy.box.Get();
      AppendOptimized(builder, boxed, stack);
    } else if e is ArraySequence<T> {
      var a := e as ArraySequence<T>;
      builder.Append(a.value);
      if 0 < stack.size {
        var next: Sequence<T> := stack.RemoveLast();
        AppendOptimized(builder, next, stack);
      }
    } else {
      SequenceTypeIsClosed(e);
      assert false;
    }
  }

  ghost function ConcatValueOnStack<T>(s: seq<Sequence<T>>): seq<T>
    requires (forall e <- s :: e.Valid())
  {
    if |s| == 0 then
      []
    else
      s[|s| - 1].Value() + ConcatValueOnStack(s[..(|s| - 1)])
  }

  ghost function SizeSum<T>(s: seq<Sequence<T>>): nat 
    requires forall e <- s :: e.Valid()
  {
    if |s| == 0 then 
      0 
    else
      var last := |s| - 1;
      SizeSum(s[..last]) + s[last].size
  }

  class LazySequence<T> extends Sequence<T> {
    ghost const value: seq<T>
    const box: AtomicBox<Sequence<T>>
    const length: nat

    ghost predicate Valid() 
      decreases size, 0
      ensures Valid() ==> 0 < size
    {
      && 0 < size
      && length == |value|
      && box.inv == (s: Sequence<T>) =>
        && s.size < size
        && s.Valid()
        && s.Value() == value
    }

    ghost predicate Call(s: Sequence<T>) {
      && s.size < size
      && s.Valid()
      && s.Value() == value
    }

    constructor(wrapped: Sequence<T>) 
      requires wrapped.Valid()
      requires 1 <= wrapped.size
      ensures Valid()
    {
      var value := wrapped.Value();
      var size := 1 + wrapped.size;
      var inv := (s: Sequence<T>) =>
        && s.size < size
        && s.Valid()
        && s.Value() == value;
      var box := AtomicBox.Make(inv, wrapped);

      this.box := box;
      this.length := wrapped.Length();
      this.value := value;
      this.size := size;
    }

    function Length(): nat 
      requires Valid() 
      decreases size, 1
    {
      length
    }
    
    ghost function Value(): seq<T> 
      requires Valid()
      decreases size, 2
      ensures |Value()| == Length()
    {
      assert |value| == Length();
      value
    }

    method ToArray() returns (ret: ImmutableArray<T>)
      requires Valid()
      decreases size, 2
      ensures ret.Valid()
      ensures ret.Length() == Length()
      ensures ret.values == Value()
    {
      var expr := box.Get();
      ret := expr.ToArray();

      var arraySeq := new ArraySequence(ret);
      box.Put(arraySeq);
    }
  }
}