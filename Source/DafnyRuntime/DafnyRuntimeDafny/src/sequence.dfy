include "../../../../Test/libraries/src/Math.dfy"

include "array.dfy"
include "frames.dfy"

module {:options "/functionSyntax:4"} Sequences {

  import Math

  import opened Frames
  import opened Arrays

  // TODO: static analysis to assert that all methods that are called directly from Dafny syntax
  // (e.g. s[i] -> s.Select(i)) have `modifies {}` (implicitly or explicitly).
  // TODO: Would also be good to assert that seq<T> is only used in specifications.
  // TODO: Align terminology between length/size/etc.
  trait Sequence<+T> extends Validatable {
   
    ghost predicate Valid()
      reads this, Repr
      decreases Repr, 0
      ensures Valid() ==> this in Repr
    
    ghost function Size(): nat
      requires Valid()
      reads this, Repr
      decreases Repr, 1
      ensures 0 < Size()

    function Length(): nat 
      requires Valid() 
      reads Repr
      decreases Repr, 1

    ghost function Value(): seq<T> 
      requires Valid()
      reads this, Repr
      decreases Repr, 2
      ensures |Value()| == Length()

    method ToArray() returns (ret: ResizableArray<T>)
      requires Valid()
      decreases Repr, 2
      ensures ret.Valid()
      ensures fresh(ret.Repr - Repr)
      ensures ret.Value() == Value()
  }

  method Concatenate<T>(left: Sequence<T>, right: Sequence<T>) returns (ret: Sequence<T>)
    requires left.Valid()
    requires right.Valid()
    requires left.Repr !! right.Repr
    ensures ret.Valid()
  {
    var c := new Concat(left, right);
    ret := new Lazy(c);
  }

  class Direct<T> extends Sequence<T> {
    const value: ResizableArray<T>

    ghost predicate Valid()
      reads this, Repr
      decreases Repr, 0
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && ValidComponent(value)
      && value.Valid()
    }

    constructor(value: ResizableArray<T>) 
      requires value.Valid()
      ensures Valid()
      ensures fresh(Repr - value.Repr)
      ensures this.value == value
    {
      this.value := value;

      Repr := {this} + value.Repr;
    }

    ghost function Size(): nat 
      requires Valid()
      reads this, Repr
      decreases Repr, 1
      ensures 0 < Size()
    {
      1
    }

    function Length(): nat 
      requires Valid() 
      reads Repr 
      decreases Repr, 1
    {
      value.size
    }

    ghost function Value(): seq<T> 
      requires Valid()
      reads this, Repr
      decreases Repr, 2
      ensures |Value()| == Length()
    {
      value.Value()
    }

    method ToArray() returns (ret: ResizableArray<T>)
      requires Valid()
      decreases Repr, 2
      ensures ret.Valid()
      ensures fresh(ret.Repr - Repr)
      ensures ret.Value() == Value()
    {
      return value;
    }
  }

  class Concat<T> extends Sequence<T> {
    const left: Sequence<T>
    const right: Sequence<T>
    const length: nat

    ghost predicate Valid() 
      reads this, Repr
      decreases Repr, 0
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && ValidComponent(left)
      && ValidComponent(right)
      && left.Repr !! right.Repr
      && length == left.Length() + right.Length()
    }

    constructor(left: Sequence<T>, right: Sequence<T>) 
      requires left.Valid()
      requires right.Valid()
      requires left.Repr !! right.Repr
      ensures Valid()
      ensures fresh(Repr - left.Repr - right.Repr)
    {
      this.left := left;
      this.right := right;
      this.length := left.Length() + right.Length();

      Repr := {this} + left.Repr + right.Repr;
    }

    ghost function Size(): nat
      requires Valid()
      reads this, Repr
      decreases Repr, 1
      ensures 0 < Size()
    {
      1 + left.Size() + right.Size()
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
      left.Value() + right.Value()
    }

    method ToArray() returns (ret: ResizableArray<T>)
      requires Valid()
      decreases Repr, 2
      ensures ret.Valid()
      ensures fresh(ret.Repr - Repr)
      ensures ret.Value() == Value()
    {
      ret := new ResizableArray<T>(length);
      var leftArray := left.ToArray();
      ret.Append(leftArray);
      var rightArray := right.ToArray();
      ret.Append(rightArray);
    }
  }

  class Lazy<T> extends Sequence<T> {
    ghost const value: seq<T>
    ghost const size: nat
    const exprBox: SequenceBox<T>
    const length: nat

    ghost predicate Valid() 
      reads this, Repr
      decreases Repr, 0
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && ValidComponent(exprBox)
      && value == exprBox.value
      && 1 <= exprBox.size
      && size == exprBox.size + 1
      && length == |value|
    }

    constructor(wrapped: Sequence<T>) 
      requires wrapped.Valid()
      requires 1 <= wrapped.Size()
      ensures Valid()
      ensures fresh(Repr - wrapped.Repr)
    {
      this.exprBox := new SequenceBox(wrapped);
      this.length := wrapped.Length();
      this.value := wrapped.Value();
      this.size := 1 + wrapped.Size();
      new;
      Repr := {this} + exprBox.Repr;
    }

    ghost function Size(): nat 
      requires Valid()
      reads this, Repr
      decreases Repr, 1
      ensures 0 < Size()
    {
      size
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
      value
    }

    method ToArray() returns (ret: ResizableArray<T>)
      requires Valid()
      decreases Repr, 2
      ensures ret.Valid()
      ensures fresh(ret.Repr - Repr)
      ensures ret.Value() == Value()
    {
      var expr := AtomicBox.Get(exprBox);
      var a := expr.ToArray();
      var direct: Direct<T> := new Direct(a);

      AtomicBox.Put(exprBox as AtomicBox<Sequence<T>>, direct.Repr, direct);

      return a;
    }
  }

  trait AtomicBox<T> extends Validatable {

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr
    }

    ghost predicate Invariant(repr: set<object>, t: T) reads repr

    // TODO: need a feasibility implementation for this somehow, pretty sure it's unsound
    static method {:extern} Put(b: AtomicBox<T>, ghost repr: set<object>, t: T)
      requires b.Invariant(repr, t)

    static method {:extern} Get(b: AtomicBox<T>) returns (t: T)
      ensures b.Invariant(b.Repr, t)
  }

  class SequenceBox<T> extends AtomicBox<Sequence<T>> {
    ghost const value: seq<T>
    ghost const size: nat
    constructor(e: Sequence<T>)
      requires e.Valid()
      ensures Valid()
      ensures fresh(Repr - e.Repr)
      ensures value == e.Value()
      ensures size == e.Size()
    {
      this.Repr := {this} + e.Repr;
      this.value := e.Value();
      this.size := e.Size();
    }
    ghost predicate Invariant(repr: set<object>, t: Sequence<T>) reads repr {
      && t in repr
      && t.Repr <= repr
      && t.Valid()
      && t.Value() == value
      && t.Size() <= size
    }
  }
}