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
   
    const size: nat

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
      var a: Direct<T> := ToArray();
      return a.value.At(index);
    }

    method ToArray() returns (ret: Sequence<T>)
      requires Valid()
      decreases size, 2
      ensures ret.Valid()
      ensures ret.Value() == Value()
      ensures ret is Direct<T>
  }

  method Concatenate<T>(left: Sequence<T>, right: Sequence<T>) returns (ret: Sequence<T>)
    requires left.Valid()
    requires right.Valid()
    ensures ret.Valid()
  {
    var c := new Concat(left, right);
    ret := new Lazy(c);
  }

  class Direct<T> extends Sequence<T> {
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

    method ToArray() returns (ret: Sequence<T>)
      requires Valid()
      decreases size, 2
      ensures ret.Valid()
      ensures ret.Value() == Value()
      ensures ret is Direct<T>
    {
      return this;
    }
  }

  class Concat<T> extends Sequence<T> {
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
      left.Value() + right.Value()
    }

    method ToArray() returns (ret: Sequence<T>)
      requires Valid()
      decreases size, 2
      ensures ret.Valid()
      ensures ret.Value() == Value()
      ensures ret is Direct<T>
    {
      var a := new ResizableArray<T>(length);
      var leftArray: Direct<T> := left.ToArray();
      a.Append(leftArray.value);
      var rightArray: Direct<T> := right.ToArray();
      a.Append(rightArray.value);
      var frozen := a.Freeze();
      ret := new Direct(frozen);
    }
  }

  class Lazy<T> extends Sequence<T> {
    ghost const value: seq<T>
    const exprBox: SequenceBox<T>
    const length: nat

    ghost predicate Valid() 
      decreases size, 0
      ensures Valid() ==> 0 < size
    {
      && size == exprBox.size + 1
      && exprBox.Valid()
      && value == exprBox.value
      && 1 <= exprBox.size
      && length == |value|
    }

    constructor(wrapped: Sequence<T>) 
      requires wrapped.Valid()
      requires 1 <= wrapped.size
      ensures Valid()
    {
      this.exprBox := new SequenceBox(wrapped);
      this.length := wrapped.Length();
      this.value := wrapped.Value();
      this.size := 1 + wrapped.size;
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
      value
    }

    method ToArray() returns (ret: Sequence<T>)
      requires Valid()
      decreases size, 2
      ensures ret.Valid()
      ensures ret.Value() == Value()
      ensures ret is Direct<T>
    {
      var expr := exprBox.Get();
      ret := expr.ToArray();

      exprBox.Put(ret);
    }
  }

  class SequenceBox<T> extends AtomicBox<Sequence<T>> {
    ghost const value: seq<T>
    ghost const size: nat
    
    ghost predicate Valid() 
      reads this, Repr
      ensures Valid() ==> Repr == {}
    {
      && Repr == {}
      && inv == (e: Sequence<T>) => 
        && e.size <= size
        && e.Valid()
        && e.Value() == value
    }

    constructor(e: Sequence<T>)
      requires e.Valid()
      ensures Valid()
      ensures value == e.Value()
      ensures size == e.size
    {
      this.Repr := {this};
      var value := e.Value();
      var size := e.size;

      this.inv := (e: Sequence<T>) => 
        && e.Valid()
        && e.size <= size
        && e.Value() == value;
      this.value := value;
      this.size := size;
      new;
      Put(e);
    }

    // Need to repeat the extern declarations to satisfy the resolver.
    // See https://github.com/dafny-lang/dafny/issues/2212.

    method {:extern} Put(t: Sequence<T>)
      requires inv(t)

    method {:extern} Get() returns (t: Sequence<T>)
      ensures inv(t)
  }
}