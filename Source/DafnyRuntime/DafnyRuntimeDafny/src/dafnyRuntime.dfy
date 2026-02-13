// Internal implementation of runtime datatypes and algorithms in Dafny.
// Although some of the code in here is likely useful for other codebases,
// it is NOT intended to be used as such in its current state.
abstract module {:options "/functionSyntax:4"} Dafny {

  // Note that the T type parameters on some types,
  // such as Sequence<T> and ImmutableArray<T>,
  // should really be +T, but that isn't yet supported.
  // Before this implementation is used in more runtimes,
  // we will need to either add that support or make adjustments
  // like downcast-cloning in some backends.

  // A trait for objects with a Valid() predicate. Necessary in order to
  // generalize some proofs, but also useful for reducing the boilerplate
  // that most such objects need to include.
  trait Validatable extends object {
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
      requires this in Repr
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

  // Defining a bounded integer newtype for lengths and indices into
  // Dafny arrays and sequences. This may be distinct from the type
  // used for indexing into native arrays or similar datatypes.
  const SIZE_T_LIMIT: nat

  // The limit has to be at least a little higher than zero
  // for basic logic to be valid.
  ghost const MIN_SIZE_T_LIMIT: nat := 128

  // Ensures a minimum for SIZE_T_LIMIT.
  // Refining modules must provide a body - an empty body is enough,
  // but only works if SIZE_T_LIMIT is defined legally.
  lemma {:axiom} EnsureSizeTLimitAboveMinimum() ensures MIN_SIZE_T_LIMIT <= SIZE_T_LIMIT

  newtype size_t = x: int | 0 <= x < SIZE_T_LIMIT witness (EnsureSizeTLimitAboveMinimum(); 0)

  const SIZE_T_MAX: size_t := (EnsureSizeTLimitAboveMinimum(); (SIZE_T_LIMIT - 1) as size_t)
  const ZERO_SIZE: size_t := (EnsureSizeTLimitAboveMinimum(); 0 as size_t)
  const ONE_SIZE: size_t := (EnsureSizeTLimitAboveMinimum(); 1 as size_t)
  const TWO_SIZE: size_t := (EnsureSizeTLimitAboveMinimum(); 2 as size_t)
  const TEN_SIZE: size_t := (EnsureSizeTLimitAboveMinimum(); 10 as size_t)

  predicate SizeAdditionInRange(a: size_t, b: size_t) {
    a as int + b as int < SIZE_T_LIMIT
  } by method {
    // This is more efficient because it doesn't use any
    // unbounded int values (typically more expensive BigInteger
    // instances in most target languages).
    return a <= SIZE_T_MAX - b;
  }

  // 
  // Native implementation of a flat, single-dimensional array.
  // We use this instead of the built-in Dafny array<T> type for two reasons,
  // both of which may be addressable in the future:
  // 
  // 1. The array<T> type does not support any bulk-assignment
  //    operations, which are important to optimize as much as possible
  //    in this performance-sensitive code.
  //    I don't think it's a safe assumption that every target language
  //    will optimize a loop over a range of array indices into an
  //    equivalent memory copy, especially since the
  //    Dafny compilation process is hardly guaranteed to produce
  //    code amenable to such optimizations. :)
  //    See https://github.com/dafny-lang/dafny/issues/2447.
  //
  // 2. Dafny arrays can be multi-dimensional, and so the native implementation
  //    of that family of types is more general than the single dimension we need here.
  //    Ideally we would be able to lift the implementation of multi-dimensional arrays
  //    based on NativeArray<T> into Dafny as well, but that is likely blocked
  //    on being able to compile the interface efficiently enough.
  //    See https://github.com/dafny-lang/dafny/issues/2749.
  //
  trait {:extern} NativeArray<T> extends Validatable {

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
      ensures ValidAndDisjoint()
      ensures Repr == old(Repr)
      ensures values == old(values)[..i] + [Set(t)] + old(values)[(i + 1)..]
      ensures Select(i) == t

    method UpdateSubarray(start: size_t, other: ImmutableArray<T>)
      requires Valid()
      requires other.Valid()
      requires start <= Length()
      requires start as int + other.Length() as int <= Length() as int
      modifies Repr
      ensures ValidAndDisjoint()
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
      // This is important, because it's tempting to just return this when possible
      // to save allocations, but that leads to inconsistencies.
      ensures ret as object != this as object
      ensures |ret.values| as size_t == size
      ensures forall i | 0 <= i < size :: ret.values[i] == values[i].value

    static method {:axiom} {:extern} Make<T>(length: size_t) returns (ret: NativeArray<T>)
      ensures ret.Valid()
      ensures fresh(ret.Repr)
      ensures ret.Length() == length

    static method {:axiom} {:extern} MakeWithPrototype<T>(length: size_t, prototype: ImmutableArray<T>) returns (ret: NativeArray<T>)
      ensures ret.Valid()
      ensures fresh(ret.Repr)
      ensures ret.Length() == length

    static method {:axiom} {:extern} MakeWithInit<T>(length: size_t, initFn: size_t -> T) returns (ret: NativeArray<T>)
      ensures ret.Valid()
      ensures fresh(ret.Repr)
      ensures ret.Length() == length
      ensures ret.values == seq(length, ((i: nat) requires 0 <= i < length as nat => Set(initFn(i as size_t))))

    static method {:axiom} {:extern} Copy<T>(other: ImmutableArray<T>) returns (ret: NativeArray<T>)
      ensures ret.Valid()
      ensures fresh(ret.Repr)
      ensures ret.values == other.CellValues()
  }

  datatype ArrayCell<T> = Set(value: T) | Unset

  // Separate type in order to have a type without a Valid() that reads {}.
  // This could easily be implemented by the same native type as NativeArray.
  // TODO: Need to make sure NativeArray.Freeze() never returns the same object,
  // as a.Freeze() == a will lead to unsoundness. Write a Dafny test first!
  trait {:extern} ImmutableArray<T> extends object {

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

  // This is internal for now but would be great to have in a shared library.
  // It could also track a start index to support Deque-style use
  // (possibly in a separate datatype to avoid the extra overhead of adding 0 all the time).
  class Vector<T> extends Validatable {
    var storage: NativeArray<T>
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
      // TODO: This is equivalent to the above four clauses
      // but I believe it doesn't get unrolled enough.
      // && ValidComponent(storage)
      && 0 <= size <= storage.Length()
      && forall i | 0 <= i < size :: storage.values[i].Set?
    }

    constructor(length: size_t)
      ensures Valid()
      ensures Value() == []
      ensures fresh(Repr)
    {
      var storage := NativeArray<T>.Make(length);
      this.storage := storage;
      size := 0;
      Repr := {this} + storage.Repr;
    }

    // Note it is important to use this constructor
    // if T may be compiled to a primitive type we want to avoid boxing,
    // such as bytes or characters!
    constructor WithPrototype(length: size_t, prototype: ImmutableArray<T>)
      ensures Valid()
      ensures Value() == []
      ensures fresh(Repr)
    {
      var storage := NativeArray<T>.MakeWithPrototype(length, prototype);
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

      var values := storage.Freeze(size);
      var newStorage := NativeArray<T>.MakeWithPrototype(newCapacity, values);
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
  // with a direct `volatile T fooBox;` in the target language.
  trait {:extern} AtomicBox<T> {

    ghost const inv: T -> bool

    ghost predicate Valid()

    static method {:axiom} {:extern} Make(ghost inv: T -> bool, t: T) returns (ret: AtomicBox<T>)
      requires inv(t)
      ensures ret.Valid()
      ensures ret.inv == inv

    method {:axiom} {:extern} Get() returns (t: T)
      requires Valid()
      ensures inv(t)

    method {:extern} Put(t: T)
      requires Valid()
      requires inv(t)
  }

  trait {:extern} Sequence<T> extends object {

    // This is only here to support the attempts some runtimes make to
    // track what sequence values are actually sequences of characters.
    // If true, the value definitely has the type seq<char>.
    // If false, the value may or may not be a string.
    // This is always false when --unicode-char is enabled,
    // since that mode no longer applies heuristics and instead
    // only relies on static information.
    var isString: bool

    // Total class instances in the tree.
    // Used in decreases clauses.
    ghost const NodeCount: nat

    ghost predicate Valid()
      decreases NodeCount, 0
      ensures Valid() ==> 0 < NodeCount

    function Cardinality(): size_t
      requires Valid()
      decreases NodeCount, 1

    ghost function Value(): seq<T>
      requires Valid()
      decreases NodeCount, 2
      ensures |Value()| < SIZE_T_LIMIT && |Value()| as size_t == Cardinality()

    // Returns an array of the same element type as this sequence.
    // Used to ensure when we create more arrays of T elements
    // that we optimize for common types like bytes and characters,
    // even though in several Dafny backends we don't have enough type information
    // at runtime from Dafny itself.
    // TypeDescriptors would be the more general solution,
    // but they are not present where we need them
    // in most backends.
    //
    // Note this is very similar to the DafnySequence.newCopier(int length)
    // method in the Java runtime.
    method PrototypeArray() returns (ret: ImmutableArray<T>)
      requires Valid()
      decreases NodeCount, 1

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
      decreases NodeCount, 2
      ensures ret.Valid()
      ensures ret.Value() == Value()[lo..]
    {
      ret := Subsequence(lo, Cardinality());
    }

    method Take(hi: size_t) returns (ret: Sequence<T>)
      requires Valid()
      requires hi <= Cardinality()
      decreases NodeCount, 2
      ensures ret.Valid()
      ensures ret.Value() == Value()[..hi]
    {
      ret := Subsequence(0, hi);
    }

    method Subsequence(lo: size_t, hi: size_t) returns (ret: Sequence<T>)
      requires Valid()
      requires lo <= hi <= Cardinality()
      decreases NodeCount, 2
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
      decreases NodeCount, 2
      ensures Valid()
      ensures ret.Valid()
      ensures ret.Length() == Cardinality()
      ensures ret.values == Value()

    // We specifically DON'T yet implement a ToString() method because that
    // doesn't help much in practice. Most runtimes implement the conversion between
    // various Dafny types and their native string type, which we don't yet model here.

    // Quantification methods

    function Elements(): Sequence<T>
      requires Valid()
    {
      this
    }

    // The following function signature is a LIE. It says that it will return a set<X>
    // for any given X and any f, but it does it only if T and X are the same type
    // and f is the identity function. Stated differently, the function return the set
    // of elements in Sequence<T>, but it can do so only if T is an equality-supporting
    // type.
    //
    // Dafny does support the UniqueElements operation (for example, when a "forall"
    // statement needs it), but will make use of it only if T is an equality-supporting
    // type. The proper way to express that in Dafny is to declare a method outside the
    // class:
    //
    //     function {:extern} UniqueElements<X(==)>(s: Sequence<X>): set<X>
    //       requires s.Valid()
    //       ensures UniqueElements(s) == set t | t in s.Value()
    //
    // However, because the Go implementation (and perhaps the implementation of other
    // targets, too) relies on the method being an instance method, there's a mismatch.
    // Thus, for now, the best way to proceed seems to be to include the additional type
    // parameter X here.
    function {:axiom} {:extern} UniqueElements<X(==)>(ghost f: T -> X): set<X>
      requires Valid() /* AND X==T AND f is the identity function, see above */
      ensures UniqueElements(f) == set t | t in Value() :: f(t)

    // Sequence creation methods

    static method Create<T>(cardinality: size_t, initFn: size_t -> T) returns (ret: Sequence<T>) {
      var a := NativeArray<T>.MakeWithInit(cardinality, initFn);
      var frozen := a.Freeze(cardinality);
      ret := new ArraySequence(frozen);
    }

    // Sequence methods that must be static because they require T to be equality-supporting

    static method {:axiom} {:extern} EqualUpTo<T(==)>(left: Sequence<T>, right: Sequence<T>, index: size_t) returns (ret: bool)
      requires left.Valid()
      requires right.Valid()
      requires index <= left.Cardinality()
      requires index <= right.Cardinality()
      ensures ret == (left.Value()[..index] == right.Value()[..index])

    static method Equal<T(==)>(left: Sequence<T>, right: Sequence<T>) returns (ret: bool)
      requires left.Valid()
      requires right.Valid()
      ensures ret == (left.Value() == right.Value())
    {
      if left.Cardinality() != right.Cardinality() {
        return false;
      }
      ret := EqualUpTo(left, right, left.Cardinality());
    }

    static method IsPrefixOf<T(==)>(left: Sequence<T>, right: Sequence<T>) returns (ret: bool)
      requires left.Valid()
      requires right.Valid()
      ensures ret == (left.Value() <= right.Value())
    {
      if right.Cardinality() < left.Cardinality() {
        return false;
      }
      ret := EqualUpTo(left, right, left.Cardinality());
    }

    static method IsProperPrefixOf<T(==)>(left: Sequence<T>, right: Sequence<T>) returns (ret: bool)
      requires left.Valid()
      requires right.Valid()
      ensures ret == (left.Value() < right.Value())
    {
      if right.Cardinality() <= left.Cardinality() {
        return false;
      }
      ret := EqualUpTo(left, right, left.Cardinality());
    }


    static predicate Contains<T(==)>(s: Sequence<T>, t: T)
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

    static method Update<T>(s: Sequence<T>, i: size_t, t: T) returns (ret: Sequence<T>)
      requires s.Valid()
      requires i < s.Cardinality()
      ensures ret.Valid()
      ensures ret.Value() == s.Value()[..i] + [t] + s.Value()[(i + 1)..]
    {
      var a := s.ToArray();
      var newValue := NativeArray<T>.Copy(a);
      newValue.Update(i, t);
      var newValueFrozen := newValue.Freeze(newValue.Length());
      ret := new ArraySequence(newValueFrozen);
    }

    static method Concatenate<T>(left: Sequence<T>, right: Sequence<T>) returns (ret: Sequence<T>)
      requires left.Valid()
      requires right.Valid()
      ensures ret.Valid()
      ensures ret.Value() == left.Value() + right.Value()
    {
      expect SizeAdditionInRange(left.Cardinality(), right.Cardinality()),
        "Concatenation result cardinality would be larger than the maximum (" + Helpers.DafnyValueToDafnyString(SIZE_T_MAX) + ")";

      // Optimize away redundant lazy wrappers
      // (which will happen a lot with chained concatenations)
      var left' := left;
      if (left is LazySequence<T>) {
        var lazyLeft := left as LazySequence<T>;
        left' := lazyLeft.box.Get();
      }

      var right' := right;
      if (right is LazySequence<T>) {
        var lazyRight := right as LazySequence<T>;
        right' := lazyRight.box.Get();
      }

      var c := new ConcatSequence(left', right');
      ret := new LazySequence(c);
    }
  }

  class ArraySequence<T> extends Sequence<T> {
    const values: ImmutableArray<T>

    method PrototypeArray() returns (ret: ImmutableArray<T>)
      requires Valid()
      decreases NodeCount, 1
    {
      return values;
    }

    ghost predicate Valid()
      decreases NodeCount, 0
      ensures Valid() ==> 0 < NodeCount
    {
      && values.Valid()
      && NodeCount == 1
    }

    constructor(value: ImmutableArray<T>, isString: bool := false)
      requires value.Valid()
      ensures Valid()
      ensures this.values == value
    {
      this.values := value;
      this.isString := isString;
      this.NodeCount := 1;
    }

    function Cardinality(): size_t
      requires Valid()
      decreases NodeCount, 1
    {
      values.Length()
    }

    ghost function Value(): seq<T>
      requires Valid()
      decreases NodeCount, 2
      ensures |Value()| < SIZE_T_LIMIT && |Value()| as size_t == Cardinality()
    {
      values.values
    }

    method ToArray() returns (ret: ImmutableArray<T>)
      requires Valid()
      decreases NodeCount, 2
      ensures ret.Valid()
      ensures ret.Length() == Cardinality()
      ensures ret.values == Value()
    {
      return values;
    }
  }

  class ConcatSequence<T> extends Sequence<T> {
    const left: Sequence<T>
    const right: Sequence<T>
    const length: size_t

    method PrototypeArray() returns (ret: ImmutableArray<T>)
      requires Valid()
      decreases NodeCount, 1
    {
      // This is arbitrary but should work well for the majority of cases,
      // and is consistent with how the Java runtime currently handles the same problem.
      ret := left.PrototypeArray();
    }

    ghost predicate Valid()
      decreases NodeCount, 0
      ensures Valid() ==> 0 < NodeCount
    {
      && NodeCount == 1 + left.NodeCount + right.NodeCount
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
      ensures Value() == left.Value() + right.Value()
    {
      this.left := left;
      this.right := right;
      this.length := left.Cardinality() + right.Cardinality();
      this.isString := left.isString || right.isString;
      this.NodeCount := 1 + left.NodeCount + right.NodeCount;
    }

    function Cardinality(): size_t
      requires Valid()
      decreases NodeCount, 1
    {
      length
    }

    ghost function Value(): seq<T>
      requires Valid()
      decreases NodeCount, 2
      ensures |Value()| < SIZE_T_LIMIT && |Value()| as size_t == Cardinality()
    {
      var ret := left.Value() + right.Value();
      assert |ret| as size_t == Cardinality();
      ret
    }

    method ToArray() returns (ret: ImmutableArray<T>)
      requires Valid()
      decreases NodeCount, 2
      ensures ret.Valid()
      ensures ret.Length() == Cardinality()
      ensures ret.values == Value()
    {
      var prototype := PrototypeArray();
      var builder := new Vector<T>.WithPrototype(length, prototype);
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
    decreases e.NodeCount
    ensures builder.ValidAndDisjoint()
    ensures e.Valid()
    ensures builder.Value() == old(builder.Value()) + e.Value()
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

  method {:tailrecursion} {:isolate_assertions} AppendOptimized<T>(builder: Vector<T>, e: Sequence<T>, stack: Vector<Sequence<T>>)
    requires e.Valid()
    requires builder.Valid()
    requires stack.Valid()
    requires builder.Repr !! stack.Repr
    requires forall expr <- stack.Value() :: expr.Valid()
    requires builder.size as int + e.Cardinality() as int + CardinalitySum(stack.Value()) < SIZE_T_LIMIT
    modifies builder.Repr, stack.Repr
    decreases e.NodeCount + NodeCountSum(stack.Value())
    ensures builder.Valid()
    ensures stack.Valid()
    ensures builder.Value() == old(builder.Value()) + e.Value() + ConcatValueOnStack(old(stack.Value()))
  {
    if e is ConcatSequence<T> {
      var concat := e as ConcatSequence<T>;
      // TODO: Come back to this - probably possible to bound size in terms of
      // Length() if we add the invariant that no leaf nodes are empty.
      expect SizeAdditionInRange(stack.size, ONE_SIZE);
      stack.AddLast(concat.right);
      label L1:
      AppendOptimized(builder, concat.left, stack);
      assert builder.Value() == old@L1(builder.Value()) + concat.left.Value() + ConcatValueOnStack(old@L1(stack.Value()));
    } else if e is LazySequence<T> {
      var lazy := e as LazySequence<T>;
      var boxed := lazy.box.Get();
      AppendOptimized(builder, boxed, stack);
      assert builder.Value() == old(builder.Value()) + boxed.Value() + ConcatValueOnStack(old(stack.Value()));
    } else if e is ArraySequence<T> {
      var a := e as ArraySequence<T>;
      builder.Append(a.values);
      if 0 < stack.size {
        var next: Sequence<T> := stack.RemoveLast();
        label L2:
        AppendOptimized(builder, next, stack);
        assert builder.Value() == old@L2(builder.Value()) + next.Value() + ConcatValueOnStack(old@L2(stack.Value()));
      }
    } else {
      // I'd prefer to just call Sequence.ToArray(),
      // but Dafny doesn't support tail recursion optimization of mutually-recursive functions.
      // Alternatively we could use a datatype, which would be a significant rewrite.
      expect false, "Unsupported Sequence implementation";
      assert builder.Value() == old(builder.Value()) + e.Value() + ConcatValueOnStack(old(stack.Value()));
    }
    assert builder.Value() == old(builder.Value()) + e.Value() + ConcatValueOnStack(old(stack.Value()));
  }

  ghost function ConcatValueOnStack<T>(s: seq<Sequence<T>>): seq<T>
    requires (forall e <- s :: e.Valid())
  {
    if |s| == 0 then
      []
    else
      s[|s| - 1].Value() + ConcatValueOnStack(s[..(|s| - 1)])
  }

  ghost function NodeCountSum<T>(s: seq<Sequence<T>>): nat
    requires forall e <- s :: e.Valid()
  {
    if |s| == 0 then
      0
    else
      var last := |s| - 1;
      NodeCountSum(s[..last]) + s[last].NodeCount
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

    method PrototypeArray() returns (ret: ImmutableArray<T>)
      requires Valid()
      decreases NodeCount, 1
    {
      var expr : Sequence<T> := box.Get();
      ret := expr.PrototypeArray();
    }

    ghost predicate Valid()
      decreases NodeCount, 0
      ensures Valid() ==> 0 < NodeCount
    {
      && 0 < NodeCount
      && |value| < SIZE_T_LIMIT
      && length == |value| as size_t
      && box.Valid()
      && box.inv == (s: Sequence<T>) =>
                      && s.NodeCount < NodeCount
                      && s.Valid()
                      && s.Value() == value
    }

    constructor(wrapped: Sequence<T>)
      requires wrapped.Valid()
      requires 1 <= wrapped.NodeCount
      ensures Valid()
      ensures Value() == wrapped.Value()
    {
      var value := wrapped.Value();
      var nodeCount := 1 + wrapped.NodeCount;
      var inv := (s: Sequence<T>) =>
          && s.NodeCount < nodeCount
          && s.Valid()
          && s.Value() == value;
      var box := AtomicBox.Make(inv, wrapped);

      this.box := box;
      this.length := wrapped.Cardinality();
      this.isString := wrapped.isString;
      this.value := value;
      this.NodeCount := nodeCount;
    }

    function Cardinality(): size_t
      requires Valid()
      decreases NodeCount, 1
    {
      length
    }

    ghost function Value(): seq<T>
      requires Valid()
      decreases NodeCount, 2
      ensures |Value()| < SIZE_T_LIMIT && |Value()| as size_t == Cardinality()
    {
      assert |value| as size_t == Cardinality();
      value
    }

    method ToArray() returns (ret: ImmutableArray<T>)
      requires Valid()
      decreases NodeCount, 2
      ensures ret.Valid()
      ensures ret.Length() == Cardinality()
      ensures ret.values == Value()
    {
      var expr : Sequence<T> := box.Get();
      if expr is ArraySequence<T> {
        return (expr as ArraySequence<T>).values;
      }
      ret := expr.ToArray();

      var arraySeq := new ArraySequence(ret);
      box.Put(arraySeq);
    }
  }

  // Helper methods from the native runtime code
  trait {:extern} Helpers {
    static function {:extern} DafnyValueToDafnyString<T>(t: T): string
  }
}
