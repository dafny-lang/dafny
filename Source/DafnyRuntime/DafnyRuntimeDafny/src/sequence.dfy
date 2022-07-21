include "../../../../Test/libraries/src/Math.dfy"

include "array.dfy"
include "atomicBox.dfy"
include "frames.dfy"

module {:options "/functionSyntax:4"} Sequences {

  import Math

  import opened Frames
  import opened Arrays
  import opened AtomicBoxes

  // TODO: static analysis to assert that all methods that are called directly from Dafny syntax
  // (e.g. s[i] -> s.Select(i)) have `modifies {}` (implicitly or explicitly).
  // TODO: Would also be good to assert that seq<T> is only used in specifications.
  // TODO: Align terminology between length/size/etc.
  trait Sequence<+T> {
   
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

    method ToArray() returns (ret: ImmutableArray<T>)
      requires Valid()
      decreases size, 2
      ensures ret.Valid()
      ensures ret.Length() == Length()
      ensures ret.values == Value()
  }

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
      var a := new ResizableArray<T>(length);
      var leftArray := left.ToArray();
      a.Append(leftArray);
      var rightArray := right.ToArray();
      a.Append(rightArray);
      ret := a.Freeze();
    }
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