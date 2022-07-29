module {:extern "Dafny"} {:options "/functionSyntax:4"} Dafny {

  // A trait for objects with a Valid() predicate. Necessary in order to
  // generalize some proofs, but also useful for reducing the boilerplate
  // that most such objects need to include.
  trait Validatable {
    // Ghost state tracking the common set of objects most
    // methods need to read.
    ghost var Repr: set<object>

    ghost predicate Valid()
      reads this, Repr
      decreases Repr, 1
      ensures Valid() ==> this in Repr

    // Convenience predicate for when your object's validity depends on one
    // or more other objects.
    ghost predicate ValidComponent(component: Validatable)
      reads this, Repr 
      decreases Repr, 0
    {
      && this in Repr
      && component in Repr
      && component.Repr <= Repr
      && this !in component.Repr
      && (assert component.Repr < Repr; component.Valid())
    }

    // Convenience predicate, since you often want to assert that 
    // new objects in Repr are fresh as well in most postconditions.
    twostate predicate ValidAndDisjoint()
      reads this, Repr
    {
      Valid() && fresh(Repr - old(Repr))
    }
  }

  // 
  // We use this instead of the built-in Dafny array<T> type for two reasons:
  // 
  // 1. Every element of an array<T> must be initialized.
  //    This means you have to provide initial values when creating one,
  //    which you can't do in generic code if your T is not auto-initializable (T(0)).
  //    This RFC proposes a way to model uninitialized storage
  //    that could be compiled to efficient enough code instead
  //    (i.e. the Unset constructor below could be marked ghost):
  //    https://github.com/dafny-lang/rfcs/pull/11
  //
  // 2. The array<T> type does not support any bulk-assignment
  //    operations, which are important to optimize as much as possible
  //    in this performance-sensitive code.
  //    I don't think it's a safe assumption that every target language
  //    will optimize a loop over a range of array indices into an
  //    equivalent memory copy, especially since the 
  //    Dafny compilation process is hardly guaranteed to produce
  //    code amenable to such optimizations. :)
  //    See https://github.com/dafny-lang/dafny/issues/2447.
  //
  // Has {:termination false} just so we can provide a feasibility implementation
  // in a different file.
  //
  // TODO: This could be a class instead, since it doesn't require variance
  trait {:extern} Array<T> extends Validatable {

    ghost var values: seq<ArrayCell<T>>

    function Length(): nat
      requires Valid()
      reads Repr
      ensures Length() == |values|

    function Read(i: nat): (ret: T)
      requires Valid()
      requires i < Length()
      requires values[i].Set?
      reads this, Repr
      ensures ret == values[i].value

    method Write(i: nat, t: T)
      requires Valid()
      requires i < Length()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures values == old(values)[..i] + [Set(t)] + old(values)[(i + 1)..]
      ensures Read(i) == t

    // TODO: Might want a copy that takes a Vector as well
    method WriteRangeArray(start: nat, other: ImmutableArray<T>)
      requires Valid()
      requires other.Valid()
      requires start <= Length()
      requires start + other.Length() <= Length()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures values == 
        old(values)[..start] + 
        other.CellValues() +
        old(values)[(start + other.Length())..]

    method Freeze(size: nat) returns (ret: ImmutableArray<T>)
      requires Valid()
      requires size <= Length()
      requires forall i | 0 <= i < size :: values[i].Set?
      // Explicitly doesn't ensure Valid()!
      ensures ret.Valid()
      ensures |ret.values| == size
      ensures forall i | 0 <= i < size :: ret.values[i] == values[i].value
  }

  datatype ArrayCell<T> = Set(value: T) | Unset

  method {:extern} NewArray<T>(length: nat) returns (ret: Array<T>)
    ensures ret.Valid()
    ensures fresh(ret.Repr)
    ensures ret.Length() == length

  // Separate type in order to have a type without a Valid()
  // that reads {}.
  trait {:extern} ImmutableArray<+T> {

    ghost const values: seq<T>

    ghost predicate Valid()

    ghost function CellValues(): seq<ArrayCell<T>> {
      seq(|values|, i requires 0 <= i < |values| => Set(values[i]))
    }

    function Length(): nat 
      requires Valid()
      ensures Length() == |values|

    function At(index: nat): T 
      requires Valid()
      requires index < |values|
      ensures At(index) == values[index]

    method Subarray(lo: nat, hi: nat) returns (ret: ImmutableArray<T>)
      requires Valid()
      requires lo <= hi <= Length()
      ensures ret.Valid()
      ensures ret.Length() == hi - lo
      ensures ret.values == values[lo..hi]
  }

  // TODO: More consistent method names.
  // This is internal for now but would be great to have in a shared library.
  // Could also track a start index to support Deque-style use
  // (possibly in a separate datatype to avoid the extra overhead of adding 0 all the time).
  class Vector<T> extends Validatable {
    var storage: Array<T>
    var size: nat

    const MIN_SIZE := 10;

    ghost predicate Valid() 
      reads this, Repr 
      decreases Repr, 1
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && storage in Repr
      && storage.Repr <= Repr
      && this !in storage.Repr
      && storage.Valid()
      // TODO: having trouble with termination on this one
      // && ValidComponent(storage)
      && 0 <= size <= storage.Length()
      && forall i | 0 <= i < size :: storage.values[i].Set?
    }

    constructor(length: nat) 
      ensures Valid()
      ensures Value() == []
      ensures fresh(Repr)
    {
      var storage := NewArray<T>(length);
      this.storage := storage;
      size := 0;
      Repr := {this} + storage.Repr;
    }

    ghost function Value(): seq<T>
      requires Valid()
      reads this, Repr
    {
      seq(size, i requires 0 <= i < size && Valid() reads this, Repr => storage.Read(i))
    }

    function At(index: nat): T 
      requires Valid()
      requires index < size
      reads this, Repr
      ensures At(index) == Value()[index]
    {
      storage.Read(index)
    }

    function Last(): T 
      requires Valid()
      requires 0 < size
      reads this, Repr
      ensures Last() == Value()[size - 1]
    {
      storage.Read(size - 1)
    }

    method AddLast(t: T) 
      requires Valid()
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Value() == old(Value()) + [t]
    {
      if size == storage.Length() {
        Reallocate(Max(MIN_SIZE, storage.Length() * 2));
      }
      storage.Write(size, t);
      size := size + 1;
    }

    function Max(a: int, b: int): int {
      if a < b then b else a
    }

    method Reallocate(newCapacity: nat) 
      requires Valid()
      requires size <= newCapacity
      modifies Repr
      ensures ValidAndDisjoint()
      ensures storage.Length() == newCapacity
      ensures Value() == old(Value())
    {
      var newStorage := NewArray<T>(newCapacity);
      var values := storage.Freeze(size);
      newStorage.WriteRangeArray(0, values);
      storage := newStorage;

      Repr := {this} + storage.Repr;
    }

    method RemoveLast() returns (t: T) 
      requires Valid()
      requires 0 < size
      modifies Repr
      ensures ValidAndDisjoint()
      ensures old(Value()) == Value() + [t]
      ensures Value() == old(Value()[..(size - 1)])
      ensures t in old(Value())
    {
      t := storage.Read(size - 1);
      size := size - 1;
    }

    method Append(other: ImmutableArray<T>) 
      requires Valid()
      requires other.Valid()
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Value() == old(Value()) + other.values
    {
      var newSize := size + other.Length();
      if storage.Length() < newSize {

        Reallocate(Max(newSize, storage.Length() * 2));
      }
      storage.WriteRangeArray(size, other);
      size := size + other.Length();
    }

    method Freeze() returns (ret: ImmutableArray<T>)
      requires Valid()
      ensures ret.Valid()
      ensures ret.values == Value()
      // Explicitly doesn't ensure Valid()!
    {
      ret := storage.Freeze(size);
    }
  }

  // A way to ensure mutable state is safe for concurrent reads and writes
  // without risk of corrupted values.
  // The external implementation of this is expected to use language features
  // such as `volatile` as necessary to ensure that partial values are never read.
  //
  // Note that it has no mutable state according to Dafny's verification model,
  // since Put modifies {}! This is safe as long as only Dafny source code calls
  // the class' methods, since Dafny ensures that all values satisfy the invariant.
  // But if you Put(t), you don't get to assume that a subsequent Get() will return t.
  // This accurately models the nondeterminism inherent to data races.
  class {:extern} AtomicBox<!T> {

    ghost const inv: T -> bool

    static method {:extern} Make(ghost inv: T -> bool, t: T) returns (ret: AtomicBox<T>)
      requires inv(t)
      ensures ret.inv == inv

    method {:extern} Get() returns (t: T)
      ensures inv(t)

    method {:extern} Put(t: T)
      requires inv(t)
  }

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
