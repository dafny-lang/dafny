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
      && component in Repr
      && component.Repr <= Repr
      && this !in component.Repr
      && component.Valid()
    }

    // Convenience predicate, since you often want to assert that 
    // new objects in Repr are fresh as well in most postconditions.
    twostate predicate ValidAndDisjoint()
      reads this, Repr
    {
      Valid() && fresh(Repr - old(Repr))
    }
  }

  module {:extern} Helpers {
    function {:extern} ToString<T>(t: T): string
    function {:extern} HashCode<T>(t: T): bv32
  }

  // Defining a bounded integer newtype for lengths and indices into
  // arrays and sequences.
  const SIZE_T_LIMIT: nat

  // Ensured by the resolver - see PlatformConstantInjector.cs
  lemma {:axiom} AboutSizeT() ensures 128 <= SIZE_T_LIMIT

  newtype size_t = x: nat | x < SIZE_T_LIMIT witness (AboutSizeT(); 0)
  const SIZE_T_MAX: size_t := (AboutSizeT(); (SIZE_T_LIMIT - 1) as size_t)

  const ZERO_SIZE: size_t := (AboutSizeT(); 0 as size_t);
  const ONE_SIZE: size_t := (AboutSizeT(); 1 as size_t);
  const TWO_SIZE: size_t := (AboutSizeT(); 2 as size_t);
  const TEN_SIZE: size_t := (AboutSizeT(); 10 as size_t);

  predicate SizeAdditionInRange(a: size_t, b: size_t) {
    a as int + b as int < SIZE_T_LIMIT
  } by method {
    // This is more efficient because it doesn't use any
    // unbounded int values (typically more expensive BigInteger
    // instances in most target languages).
    return a <= SIZE_T_MAX - b;
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
  // TODO: This could be a class instead, since it doesn't require variance.
  // A trait does allow more than one implementation though.
  // TODO: Be clearer this is a one-dimensional array.
  trait {:extern} Array<T> extends Validatable {

    ghost var values: seq<ArrayCell<T>>

    ghost predicate Valid()
      reads this, Repr
      decreases Repr, 1
      ensures Valid() ==> this in Repr
      ensures Valid() ==> |values| < SIZE_T_LIMIT

    function Length(): size_t
      requires Valid()
      reads Repr
      ensures Length() == |values| as size_t

    function Select(i: size_t): (ret: T)
      requires Valid()
      requires i < Length()
      requires values[i].Set?
      reads this, Repr
      ensures ret == values[i].value

    method Update(i: size_t, t: T)
      requires Valid()
      requires i < Length()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures values == old(values)[..i] + [Set(t)] + old(values)[(i + 1)..]
      ensures Select(i) == t

    method UpdateSubarray(start: size_t, other: ImmutableArray<T>)
      requires Valid()
      requires other.Valid()
      requires start <= Length()
      requires start as int + other.Length() as int <= Length() as int
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures values == 
        old(values)[..start] + 
        other.CellValues() +
        old(values)[(start + other.Length())..]

    method Freeze(size: size_t) returns (ret: ImmutableArray<T>)
      requires Valid()
      requires size <= Length()
      requires forall i | 0 <= i < size :: values[i].Set?
      // Explicitly doesn't ensure Valid()!
      ensures ret.Valid()
      ensures |ret.values| as size_t == size
      ensures forall i | 0 <= i < size :: ret.values[i] == values[i].value
  }

  datatype ArrayCell<T> = Set(value: T) | Unset

  // Takes a nat rather than a size_t because Dafny won't verify the limit for you.
  // Instead the extern implementation needs to halt if the value is too big
  // (or if there isn't adequate memory to allocate).
  // By contrast, the methods on [Immutable]Array can safely assume that
  // unbounded int values can be downcast to size_t, since Dafny WILL verify that
  // all indices are in bounds and hence less than SIZE_T_MAX.
  method {:extern} NewArray<T>(length: nat) returns (ret: Array<T>)
    ensures ret.Valid()
    ensures fresh(ret.Repr)
    ensures ret.Length() as nat == length

  method {:extern} CopyArray<T>(other: ImmutableArray<T>) returns (ret: Array<T>)
    ensures ret.Valid()
    ensures fresh(ret.Repr)
    ensures ret.values == other.CellValues()

  // Separate type in order to have a type without a Valid()
  // that reads {}.
  trait {:extern} ImmutableArray<+T> {

    ghost const values: seq<T>

    ghost predicate Valid()
      ensures Valid() ==> |values| < SIZE_T_LIMIT

    ghost function CellValues(): seq<ArrayCell<T>> {
      seq(|values|, i requires 0 <= i < |values| => Set(values[i]))
    }

    function Length(): size_t 
      requires Valid()
      ensures Length() == |values| as size_t

    function Select(index: size_t): T 
      requires Valid()
      requires index < |values| as size_t
      ensures Select(index) == values[index]

    method Subarray(lo: size_t, hi: size_t) returns (ret: ImmutableArray<T>)
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
    // TODO: "length"?
    var size: size_t

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

    constructor(length: size_t) 
      ensures Valid()
      ensures Value() == []
      ensures fresh(Repr)
    {
      var storage := NewArray<T>(length as nat);
      this.storage := storage;
      size := 0;
      Repr := {this} + storage.Repr;
    }

    ghost function Value(): seq<T>
      requires Valid()
      reads this, Repr
    {
      seq(size, i requires 0 <= i < size as int && Valid() reads this, Repr => storage.Select(i as size_t))
    }

    function Select(index: size_t): T 
      requires Valid()
      requires index < size
      reads this, Repr
      ensures Select(index) == Value()[index]
    {
      storage.Select(index)
    }

    function Last(): T 
      requires Valid()
      requires 0 < size
      reads this, Repr
      ensures Last() == Value()[size - 1]
    {
      storage.Select(size - 1)
    }

    method AddLast(t: T) 
      requires Valid()
      requires size as int + 1 < SIZE_T_LIMIT
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Value() == old(Value()) + [t]
    {
      EnsureCapacity(size + ONE_SIZE);
      storage.Update(size, t);
      size := size + 1;
    }

    function Max(a: size_t, b: size_t): size_t {
      if a < b then b else a
    }

    method EnsureCapacity(newMinCapacity: size_t) 
      requires Valid()
      modifies Repr
      ensures ValidAndDisjoint()
      ensures storage.Length() >= newMinCapacity
      ensures Value() == old(Value())
    {
      if storage.Length() >= newMinCapacity {
        return;
      }

      var newCapacity := newMinCapacity;
      if storage.Length() <= SIZE_T_MAX / TWO_SIZE {
        newCapacity := Max(newCapacity, storage.Length() * TWO_SIZE);
      }

      var newStorage := NewArray<T>(newCapacity as nat);
      var values := storage.Freeze(size);
      newStorage.UpdateSubarray(0, values);
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
      t := storage.Select(size - 1);
      size := size - 1;
    }

    method Append(other: ImmutableArray<T>) 
      requires Valid()
      requires other.Valid()
      requires size as int + other.Length() as int < SIZE_T_LIMIT
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Value() == old(Value()) + other.values
    {
      var newSize := size + other.Length();
      EnsureCapacity(newSize);
      storage.UpdateSubarray(size, other);
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
  //
  // Compilers could special case this type to inline declarations and avoid
  // the cost of allocation and indirection, e.g. by replacing a `const fooBox: AtomicBox<T>`
  // with a direct `volitile T fooBox;` in the target language.
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

  // TODO: Need custom compiler/runtime code to connect things like HashCode(), Equals() and ToString()
  // to the native versions of those concepts, adjusting for names and native string types.
  // The answer is likely to make sure all target languages support classes with a mix of Dafny- and 
  // target language-defined methods (which Go doesn't yet support, and I don't think C++ does either).
  // If we ever target a language that really can't support this, the worst case option is to
  // not rely on built-in functionality that requires those built-in methods to be implemented.
  //
  // TODO: How to deal with iteration (for quantification)? Again we could rely on target-language
  // code to add iterator() implementations as necessary...
  //
  // TODO: static analysis to assert that all methods that are called directly from Dafny syntax
  // (e.g. s[i] -> s.Select(i)) have `modifies {}` (implicitly or explicitly).
  // TODO: Would also be good to assert that seq<T> is only used in specifications.
  // TODO: Align terminology between length/size/etc.
  trait {:extern} Sequence<+T> {
   
    // TODO: Better name, NOT a size_t
    ghost const size: nat

    ghost predicate Valid()
      decreases size, 0
      ensures Valid() ==> 0 < size
    
    function Cardinality(): size_t 
      requires Valid() 
      decreases size, 1

    ghost function Value(): seq<T> 
      requires Valid()
      decreases size, 2
      ensures |Value()| < SIZE_T_LIMIT && |Value()| as size_t == Cardinality()

    method HashCode() returns (ret: bv32)
      requires Valid()
      // TODO: function version as specification (or function by method)
    {
      ret := 0;
      for i := ZERO_SIZE to Cardinality() {
        var element := Select(i);
        ret := ((ret << 3) | (ret >> 29)) ^ Helpers.HashCode(element);
      }
    }

    method ToString() returns (ret: string)
      requires Valid()
    {
      // TODO: Can we use compiled seq<T> values like this?
      // TODO: Need to track whether this is a seq<char> at runtime
      ret := "[";
      for i := ZERO_SIZE to Cardinality() {
        if i != 0 {
          ret := ret + ",";
        }
        var element := Select(i as size_t);
        ret := ret + Helpers.ToString(element);
      }
      ret := ret + "]";
    }

    method Select(index: size_t) returns (ret: T)
      requires Valid()
      requires index < Cardinality()
      ensures ret == Value()[index]
    {
      var a := ToArray();
      return a.Select(index);
    }

    method Drop(lo: size_t) returns (ret: Sequence<T>)
      requires Valid()
      requires lo <= Cardinality()
      decreases size, 2
      ensures ret.Valid()
      ensures ret.Value() == Value()[lo..]
    {
      ret := Subsequence(lo, Cardinality());
    }

    method Take(hi: size_t) returns (ret: Sequence<T>)
      requires Valid()
      requires hi <= Cardinality()
      decreases size, 2
      ensures ret.Valid()
      ensures ret.Value() == Value()[..hi]
    {
      ret := Subsequence(0, hi);
    }

    method Subsequence(lo: size_t, hi: size_t) returns (ret: Sequence<T>)
      requires Valid()
      requires lo <= hi <= Cardinality()
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
      ensures ret.Length() == Cardinality()
      ensures ret.values == Value()
  }

  // TODO: this would be safe(r) if we used a datatype instead, but still not guaranteed.
  // Is there a decent solution in every target language?
  // TODO: Eliminate this, so that it is sound to provide a native language implementation
  // (in particular, wrapping a native string type as a seq<char>).
  lemma {:axiom} SequenceTypeIsClosed<T>(e: Sequence<T>) 
    ensures
      || e is ArraySequence<T>
      || e is ConcatSequence<T>
      || e is LazySequence<T>

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

    function Cardinality(): size_t 
      requires Valid() 
      decreases size, 1
    {
      value.Length()
    }

    ghost function Value(): seq<T> 
      requires Valid()
      decreases size, 2
      ensures |Value()| < SIZE_T_LIMIT && |Value()| as size_t == Cardinality()
    {
      value.values
    }

    method ToArray() returns (ret: ImmutableArray<T>)
      requires Valid()
      decreases size, 2
      ensures ret.Valid()
      ensures ret.Length() == Cardinality()
      ensures ret.values == Value()
    {
      return value;
    }
  }

  class ConcatSequence<T> extends Sequence<T> {
    const left: Sequence<T>
    const right: Sequence<T>
    const length: size_t

    ghost predicate Valid() 
      decreases size, 0
      ensures Valid() ==> 0 < size
    {
      && size == 1 + left.size + right.size
      && left.Valid()
      && right.Valid()
      && left.Cardinality() as int + right.Cardinality() as int < SIZE_T_LIMIT as int
      && length == left.Cardinality() + right.Cardinality()
    }

    constructor(left: Sequence<T>, right: Sequence<T>) 
      requires left.Valid()
      requires right.Valid()
      requires left.Cardinality() as int + right.Cardinality() as int < SIZE_T_LIMIT as int
      ensures Valid()
    {
      this.left := left;
      this.right := right;
      this.length := left.Cardinality() + right.Cardinality();
      this.size := 1 + left.size + right.size;
    }

    function Cardinality(): size_t 
      requires Valid() 
      decreases size, 1
    {
      length
    }

    ghost function Value(): seq<T> 
      requires Valid()
      decreases size, 2
      ensures |Value()| < SIZE_T_LIMIT && |Value()| as size_t == Cardinality()
    {
      var ret := left.Value() + right.Value();
      assert |ret| as size_t == Cardinality();
      ret
    }

    method ToArray() returns (ret: ImmutableArray<T>)
      requires Valid()
      decreases size, 2
      ensures ret.Valid()
      ensures ret.Length() == Cardinality()
      ensures ret.values == Value()
    {
      var builder := new Vector<T>(length);
      var stack := new Vector<Sequence<T>>(TEN_SIZE);
      AppendOptimized(builder, this, stack);
      ret := builder.Freeze();
    }
  }

  // Simpler reference implementation of AppendOptimized
  method AppendRecursive<T>(builder: Vector<T>, e: Sequence<T>)
    requires e.Valid()
    requires builder.Valid()
    requires SizeAdditionInRange(builder.size, e.Cardinality())
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
    requires builder.size as int + e.Cardinality() as int + CardinalitySum(stack.Value()) < SIZE_T_LIMIT
    modifies builder.Repr, stack.Repr
    decreases e.size + SizeSum(stack.Value())
    ensures builder.Valid()
    ensures stack.Valid()
    ensures builder.Value() == old(builder.Value()) + e.Value() + ConcatValueOnStack(old(stack.Value()));
  {
    if e is ConcatSequence<T> {
      var concat := e as ConcatSequence<T>;
      // TODO: Come back to this - probably possible to bound size in terms of
      // Length() if we add the invariant that no leave nodes are empty.
      expect SizeAdditionInRange(stack.size, ONE_SIZE);
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

  ghost function CardinalitySum<T>(s: seq<Sequence<T>>): nat 
    requires forall e <- s :: e.Valid()
  {
    if |s| == 0 then 
      0 
    else
      var last := |s| - 1;
      CardinalitySum(s[..last]) + s[last].Cardinality() as nat
  }

  class LazySequence<T> extends Sequence<T> {
    ghost const value: seq<T>
    const box: AtomicBox<Sequence<T>>
    const length: size_t

    ghost predicate Valid() 
      decreases size, 0
      ensures Valid() ==> 0 < size
    {
      && 0 < size
      && |value| < SIZE_T_LIMIT
      && length == |value| as size_t
      && box.inv == (s: Sequence<T>) =>
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
      this.length := wrapped.Cardinality();
      this.value := value;
      this.size := size;
    }

    function Cardinality(): size_t 
      requires Valid() 
      decreases size, 1
    {
      length
    }
    
    ghost function Value(): seq<T> 
      requires Valid()
      decreases size, 2
      ensures |Value()| < SIZE_T_LIMIT && |Value()| as size_t == Cardinality()
    {
      assert |value| as size_t == Cardinality();
      value
    }

    method ToArray() returns (ret: ImmutableArray<T>)
      requires Valid()
      decreases size, 2
      ensures ret.Valid()
      ensures ret.Length() == Cardinality()
      ensures ret.values == Value()
    {
      var expr := box.Get();
      ret := expr.ToArray();

      var arraySeq := new ArraySequence(ret);
      box.Put(arraySeq);
    }
  }

  // Sequence methods that must be static because they require T to be equality-supporting

  method EqualUpTo<T(==)>(left: Sequence<T>, right: Sequence<T>, index: size_t) returns (ret: bool) 
    requires left.Valid()
    requires right.Valid()
    requires index <= left.Cardinality()
    requires index <= right.Cardinality()
    ensures ret == (left.Value()[..index] == right.Value()[..index])
  {
    for i := 0 to index
      invariant left.Value()[..i] == right.Value()[..i]
    {
      var leftElement := left.Select(i);
      var rightElement := right.Select(i);
      if leftElement != rightElement {
        return false;
      }
    }
    return true;
  }

  method EqualSequences<T(==)>(left: Sequence<T>, right: Sequence<T>) returns (ret: bool) 
    requires left.Valid()
    requires right.Valid()
    ensures ret == (left.Value() == right.Value())
  {
    if left.Cardinality() != right.Cardinality() {
      return false;
    }
    ret := EqualUpTo(left, right, left.Cardinality());
  }

  method IsPrefixOf<T(==)>(left: Sequence<T>, right: Sequence<T>) returns (ret: bool) 
    requires left.Valid()
    requires right.Valid()
    ensures ret == (left.Value() <= right.Value())
  {
    if right.Cardinality() < left.Cardinality() {
      return false;
    }
    ret := EqualUpTo(left, right, left.Cardinality());
  }

  method IsProperPrefixOf<T(==)>(left: Sequence<T>, right: Sequence<T>) returns (ret: bool) 
    requires left.Valid()
    requires right.Valid()
    ensures ret == (left.Value() < right.Value())
  {
    if right.Cardinality() <= left.Cardinality() {
      return false;
    }
    ret := EqualUpTo(left, right, left.Cardinality());
  }


  predicate Contains<T(==)>(s: Sequence<T>, t: T)
    requires s.Valid()
  {
    t in s.Value()
  } by method {
    for i := ZERO_SIZE to s.Cardinality() 
      invariant t !in s.Value()[..i]
    {
      var element := s.Select(i);
      if element == t {
        return true;
      }
    }
    return false;
  }

  // Sequence methods that must be static because they use T as an in-parameter

  method Concatenate<T>(left: Sequence<T>, right: Sequence<T>) returns (ret: Sequence<T>)
    requires left.Valid()
    requires right.Valid()
    ensures ret.Valid()
  {
    expect SizeAdditionInRange(left.Cardinality(), right.Cardinality()), "Concatenation result cardinality would be larger than the maximum (" + Helpers.ToString(SIZE_T_MAX) + ")";

    // TODO: This could inspect left and right to see if they are already LazySequences
    // and concatenate the boxed values if so.
    var c := new ConcatSequence(left, right);
    ret := new LazySequence(c);
  }

  method Update<T>(s: Sequence<T>, i: size_t, t: T) returns (ret: Sequence<T>)
    requires s.Valid()
    requires i < s.Cardinality()
    ensures ret.Valid()
    ensures ret.Value() == s.Value()[..i] + [t] + s.Value()[(i + 1)..]
  {
    var a := s.ToArray();
    var newValue := CopyArray(a);
    newValue.Update(i, t);
    var newValueFrozen := newValue.Freeze(newValue.Length());
    ret := new ArraySequence(newValueFrozen);
  }
}
