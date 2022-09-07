// Dafny program dafnyRuntime.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// Dafny 3.7.2.40713
// Command Line Options: /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/dafnyRuntime.dfy /compileTarget:cs /out:../DafnyRuntime/generated
// dafnyRuntime.dfy


module {:extern ""Dafny""} {:options ""/functionSyntax:4""} Dafny {
  trait Validatable {
    ghost var Repr: set<object>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr, 1

    predicate ValidComponent(component: Validatable)
      reads this, Repr
      decreases Repr, 0
    {
      component in Repr &&
      component.Repr <= Repr &&
      this !in component.Repr &&
      component.Valid()
    }

    twostate predicate ValidAndDisjoint()
      reads this, Repr
      decreases Repr + {this}
    {
      Valid() &&
      fresh(Repr - old(Repr))
    }
  }

  module {:extern} Helpers {
    function method {:extern} ToString<T>(t: T): string

    function method {:extern} HashCode<T>(t: T): bv32
  }

  trait {:extern} Array<T> extends Validatable {
    ghost var values: seq<ArrayCell<T>>

    function method Length(): nat
      requires Valid()
      reads Repr
      ensures Length() == |values|
      decreases Repr

    function method Select(i: nat): (ret: T)
      requires Valid()
      requires i < Length()
      requires values[i].Set?
      reads this, Repr
      ensures ret == values[i].value
      decreases Repr + {this}, i

    method Update(i: nat, t: T)
      requires Valid()
      requires i < Length()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures values == old(values)[..i] + [Set(t)] + old(values)[i + 1..]
      ensures Select(i) == t
      decreases i

    method UpdateSubarray(start: nat, other: ImmutableArray<T>)
      requires Valid()
      requires other.Valid()
      requires start <= Length()
      requires start + other.Length() <= Length()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures values == old(values)[..start] + other.CellValues() + old(values)[start + other.Length()..]
      decreases start, other

    method Freeze(size: nat) returns (ret: ImmutableArray<T>)
      requires Valid()
      requires size <= Length()
      requires forall i: int | 0 <= i < size :: values[i].Set?
      ensures ret.Valid()
      ensures |ret.values| == size
      ensures forall i: int | 0 <= i < size :: ret.values[i] == values[i].value
      decreases size
  }

  datatype ArrayCell<T> = Set(value: T) | Unset

  trait {:extern} ImmutableArray<+T> {
    ghost const values: seq<T>

    predicate Valid()

    function CellValues(): seq<ArrayCell<T>>
    {
      seq(|values|, (i: int) requires 0 <= i < |values| => Set(values[i]))
    }

    function method Length(): nat
      requires Valid()
      ensures Length() == |values|

    function method Select(index: nat): T
      requires Valid()
      requires index < |values|
      ensures Select(index) == values[index]
      decreases index

    method Subarray(lo: nat, hi: nat) returns (ret: ImmutableArray<T>)
      requires Valid()
      requires lo <= hi <= Length()
      ensures ret.Valid()
      ensures ret.Length() == hi - lo
      ensures ret.values == values[lo .. hi]
      decreases lo, hi
  }

  class Vector<T> extends Validatable {
    var storage: Array<T>
    var size: nat
    const MIN_SIZE := 10

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr, 1
    {
      this in Repr &&
      storage in Repr &&
      storage.Repr <= Repr &&
      this !in storage.Repr &&
      storage.Valid() &&
      0 <= size <= storage.Length() &&
      forall i: int | 0 <= i < size :: 
        storage.values[i].Set?
    }

    constructor (length: nat)
      ensures Valid()
      ensures Value() == []
      ensures fresh(Repr)
      decreases length
    {
      var storage := NewArray<T>(length);
      this.storage := storage;
      size := 0;
      Repr := {this} + storage.Repr;
    }

    function Value(): seq<T>
      requires Valid()
      reads this, Repr
      decreases Repr + {this}
    {
      seq(size, (i: int) requires 0 <= i < size && Valid() reads this, Repr => storage.Select(i))
    }

    function method Select(index: nat): T
      requires Valid()
      requires index < size
      reads this, Repr
      ensures Select(index) == Value()[index]
      decreases Repr + {this}, index
    {
      storage.Select(index)
    }

    function method Last(): T
      requires Valid()
      requires 0 < size
      reads this, Repr
      ensures Last() == Value()[size - 1]
      decreases Repr + {this}
    {
      storage.Select(size - 1)
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
      storage.Update(size, t);
      size := size + 1;
    }

    function method Max(a: int, b: int): int
      decreases a, b
    {
      if a < b then
        b
      else
        a
    }

    method Reallocate(newCapacity: nat)
      requires Valid()
      requires size <= newCapacity
      modifies Repr
      ensures ValidAndDisjoint()
      ensures storage.Length() == newCapacity
      ensures Value() == old(Value())
      decreases newCapacity
    {
      var newStorage := NewArray<T>(newCapacity);
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
      ensures Value() == old(Value()[..size - 1])
      ensures t in old(Value())
    {
      t := storage.Select(size - 1);
      size := size - 1;
    }

    method Append(other: ImmutableArray<T>)
      requires Valid()
      requires other.Valid()
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Value() == old(Value()) + other.values
      decreases other
    {
      var newSize := size + other.Length();
      if storage.Length() < newSize {
        Reallocate(Max(newSize, storage.Length() * 2));
      }
      storage.UpdateSubarray(size, other);
      size := size + other.Length();
    }

    method Freeze() returns (ret: ImmutableArray<T>)
      requires Valid()
      ensures ret.Valid()
      ensures ret.values == Value()
    {
      ret := storage.Freeze(size);
    }
  }

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

  trait {:extern} Sequence<+T> {
    ghost const size: nat

    predicate Valid()
      ensures Valid() ==> 0 < size
      decreases size, 0

    function method Length(): nat
      requires Valid()
      decreases size, 1

    function Value(): seq<T>
      requires Valid()
      ensures |Value()| == Length()
      decreases size, 2

    method HashCode() returns (ret: bv32)
      requires Valid()
    {
      ret := 0;
      for i: int := 0 to Length() {
        var element := Select(i);
        ret := ((ret << 3) | (ret >> 29)) ^ Helpers.HashCode(element);
      }
    }

    method ToString() returns (ret: string)
      requires Valid()
    {
      ret := ""["";
      for i: int := 0 to Length() {
        if i != 0 {
          ret := ret + "","";
        }
        var element := Select(i);
        ret := ret + Helpers.ToString(element);
      }
      ret := ret + ""]"";
    }

    method Select(index: nat) returns (ret: T)
      requires Valid()
      requires index < Length()
      ensures ret == Value()[index]
      decreases index
    {
      var a := ToArray();
      return a.Select(index);
    }

    method Drop(lo: nat) returns (ret: Sequence<T>)
      requires Valid()
      requires lo <= Length()
      ensures ret.Valid()
      ensures ret.Value() == Value()[lo..]
      decreases size, 2
    {
      ret := Subsequence(lo, Length());
    }

    method Take(hi: nat) returns (ret: Sequence<T>)
      requires Valid()
      requires hi <= Length()
      ensures ret.Valid()
      ensures ret.Value() == Value()[..hi]
      decreases size, 2
    {
      ret := Subsequence(0, hi);
    }

    method Subsequence(lo: nat, hi: nat) returns (ret: Sequence<T>)
      requires Valid()
      requires lo <= hi <= Length()
      ensures ret.Valid()
      ensures ret.Value() == Value()[lo .. hi]
      decreases size, 2
    {
      var a := ToArray();
      var subarray := a.Subarray(lo, hi);
      ret := new ArraySequence<T>(subarray);
    }

    method ToArray() returns (ret: ImmutableArray<T>)
      requires Valid()
      ensures ret.Valid()
      ensures ret.Length() == Length()
      ensures ret.values == Value()
      decreases size, 2
  }

  class ArraySequence<T> extends Sequence<T> {
    const value: ImmutableArray<T>

    predicate Valid()
      ensures Valid() ==> 0 < size
      decreases size, 0
    {
      value.Valid() &&
      size == 1
    }

    constructor (value: ImmutableArray<T>)
      requires value.Valid()
      ensures Valid()
      ensures this.value == value
      decreases value
    {
      this.value := value;
      this.size := 1;
    }

    function method Length(): nat
      requires Valid()
      decreases size, 1
    {
      value.Length()
    }

    function Value(): seq<T>
      requires Valid()
      ensures |Value()| == Length()
      decreases size, 2
    {
      value.values
    }

    method ToArray() returns (ret: ImmutableArray<T>)
      requires Valid()
      ensures ret.Valid()
      ensures ret.Length() == Length()
      ensures ret.values == Value()
      decreases size, 2
    {
      return value;
    }
  }

  class ConcatSequence<T> extends Sequence<T> {
    const left: Sequence<T>
    const right: Sequence<T>
    const length: nat

    predicate Valid()
      ensures Valid() ==> 0 < size
      decreases size, 0
    {
      size == 1 + left.size + right.size &&
      left.Valid() &&
      right.Valid() &&
      length == left.Length() + right.Length()
    }

    constructor (left: Sequence<T>, right: Sequence<T>)
      requires left.Valid()
      requires right.Valid()
      ensures Valid()
      decreases left, right
    {
      this.left := left;
      this.right := right;
      this.length := left.Length() + right.Length();
      this.size := 1 + left.size + right.size;
    }

    function method Length(): nat
      requires Valid()
      decreases size, 1
    {
      length
    }

    function Value(): seq<T>
      requires Valid()
      ensures |Value()| == Length()
      decreases size, 2
    {
      ghost var ret: seq<T> := left.Value() + right.Value();
      assert |ret| == Length();
      ret
    }

    method ToArray() returns (ret: ImmutableArray<T>)
      requires Valid()
      ensures ret.Valid()
      ensures ret.Length() == Length()
      ensures ret.values == Value()
      decreases size, 2
    {
      var builder := new Vector<T>(length);
      var stack := new Vector<Sequence<T>>(10);
      AppendOptimized(builder, this, stack);
      ret := builder.Freeze();
    }
  }

  class LazySequence<T> extends Sequence<T> {
    ghost const value: seq<T>
    const box: AtomicBox<Sequence<T>>
    const length: nat

    predicate Valid()
      ensures Valid() ==> 0 < size
      decreases size, 0
    {
      0 < size &&
      length == |value| &&
      box.inv == (s: Sequence<T>) => s.size < size && s.Valid() && s.Value() == value
    }

    constructor (wrapped: Sequence<T>)
      requires wrapped.Valid()
      requires 1 <= wrapped.size
      ensures Valid()
      decreases wrapped
    {
      ghost var value := wrapped.Value();
      ghost var size := 1 + wrapped.size;
      ghost var inv := (s: Sequence<T>) => s.size < size && s.Valid() && s.Value() == value;
      var box := AtomicBox.Make(inv, wrapped);
      this.box := box;
      this.length := wrapped.Length();
      this.value := value;
      this.size := size;
    }

    function method Length(): nat
      requires Valid()
      decreases size, 1
    {
      length
    }

    function Value(): seq<T>
      requires Valid()
      ensures |Value()| == Length()
      decreases size, 2
    {
      assert |value| == Length();
      value
    }

    method ToArray() returns (ret: ImmutableArray<T>)
      requires Valid()
      ensures ret.Valid()
      ensures ret.Length() == Length()
      ensures ret.values == Value()
      decreases size, 2
    {
      var expr := box.Get();
      ret := expr.ToArray();
      var arraySeq := new ArraySequence<T>(ret);
      box.Put(arraySeq);
    }
  }

  method {:extern} NewArray<T>(length: nat) returns (ret: Array<T>)
    ensures ret.Valid()
    ensures fresh(ret.Repr)
    ensures ret.Length() == length
    decreases length

  method {:extern} CopyArray<T>(other: ImmutableArray<T>) returns (ret: Array<T>)
    ensures ret.Valid()
    ensures fresh(ret.Repr)
    ensures ret.values == other.CellValues()
    decreases other

  lemma {:axiom} SequenceTypeIsClosed<T>(e: Sequence<T>)
    ensures e is ArraySequence<T> || e is ConcatSequence<T> || e is LazySequence<T>
    decreases e

  method AppendRecursive<T>(builder: Vector<T>, e: Sequence<T>)
    requires e.Valid()
    requires builder.Valid()
    modifies builder.Repr
    ensures builder.ValidAndDisjoint()
    ensures e.Valid()
    ensures builder.Value() == old(builder.Value()) + e.Value()
    decreases e.size
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
    requires builder.Repr !! stack.Repr
    requires forall expr: Sequence<T> | expr in stack.Value() :: expr.Valid()
    modifies builder.Repr, stack.Repr
    ensures builder.Valid()
    ensures stack.Valid()
    ensures builder.Value() == old(builder.Value()) + e.Value() + ConcatValueOnStack(old(stack.Value()))
    decreases e.size + SizeSum(stack.Value())
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

  function ConcatValueOnStack<T>(s: seq<Sequence<T>>): seq<T>
    requires forall e: Sequence<T> | e in s :: e.Valid()
    decreases s
  {
    if |s| == 0 then
      []
    else
      s[|s| - 1].Value() + ConcatValueOnStack(s[..|s| - 1])
  }

  function SizeSum<T>(s: seq<Sequence<T>>): nat
    requires forall e: Sequence<T> | e in s :: e.Valid()
    decreases s
  {
    if |s| == 0 then
      0
    else
      ghost var last: int := |s| - 1; SizeSum(s[..last]) + s[last].size
  }

  method EqualUpTo<T(==)>(left: Sequence<T>, right: Sequence<T>, index: nat)
      returns (ret: bool)
    requires left.Valid()
    requires right.Valid()
    requires index <= left.Length()
    requires index <= right.Length()
    ensures ret == (left.Value()[..index] == right.Value()[..index])
    decreases left, right, index
  {
    for i: int := 0 to index
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
    decreases left, right
  {
    if left.Length() != right.Length() {
      return false;
    }
    ret := EqualUpTo(left, right, left.Length());
  }

  method IsPrefixOf<T(==)>(left: Sequence<T>, right: Sequence<T>) returns (ret: bool)
    requires left.Valid()
    requires right.Valid()
    ensures ret == (left.Value() <= right.Value())
    decreases left, right
  {
    if right.Length() < left.Length() {
      return false;
    }
    ret := EqualUpTo(left, right, left.Length());
  }

  method IsProperPrefixOf<T(==)>(left: Sequence<T>, right: Sequence<T>) returns (ret: bool)
    requires left.Valid()
    requires right.Valid()
    ensures ret == (left.Value() < right.Value())
    decreases left, right
  {
    if right.Length() <= left.Length() {
      return false;
    }
    ret := EqualUpTo(left, right, left.Length());
  }

  predicate Contains<T(==)>(s: Sequence<T>, t: T)
    requires s.Valid()
    decreases s
  {
    t in s.Value()
  } by method {
    for i: int := 0 to s.Length()
      invariant t !in s.Value()[..i]
    {
      var element := s.Select(i);
      if element == t {
        return true;
      }
    }
    return false;
  }

  method Concatenate<T>(left: Sequence<T>, right: Sequence<T>) returns (ret: Sequence<T>)
    requires left.Valid()
    requires right.Valid()
    ensures ret.Valid()
    decreases left, right
  {
    var c := new ConcatSequence<T>(left, right);
    ret := new LazySequence<T>(c);
  }

  method Update<T>(s: Sequence<T>, i: nat, t: T)
      returns (ret: Sequence<T>)
    requires s.Valid()
    requires i < s.Length()
    ensures ret.Valid()
    ensures ret.Value() == s.Value()[..i] + [t] + s.Value()[i + 1..]
    decreases s, i
  {
    var a := s.ToArray();
    var newValue := CopyArray(a);
    newValue.Update(i, t);
    var newValueFrozen := newValue.Freeze(newValue.Length());
    ret := new ArraySequence<T>(newValueFrozen);
  }

  method MultiDimentionalArrays()
  {
    var a := new int[3, 4, 5] ((i: nat, j: int, k: int) => 0);
    a[1, 1, 1] := 42;
  }
}
")]

namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
    public static T[,,] InitNewArray3<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      T[,,] a = new T[s0,s1,s2];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            a[i0,i1,i2] = z;
          }
        }
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
}
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace _System
namespace Helpers_Compile {

} // end of namespace Helpers_Compile
namespace Dafny {

  public interface Validatable {
  }
  public class _Companion_Validatable {
  }

  public interface Array<T> : Dafny.Validatable {
    BigInteger Length();
    T Select(BigInteger i);
    void Update(BigInteger i, T t);
    void UpdateSubarray(BigInteger start, Dafny.ImmutableArray<T> other);
    Dafny.ImmutableArray<T> Freeze(BigInteger size);
  }
  public class _Companion_Array<T> {
  }

  public interface _IArrayCell<T> {
    bool is_Set { get; }
    bool is_Unset { get; }
    T dtor_value { get; }
    _IArrayCell<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public abstract class ArrayCell<T> : _IArrayCell<T> {
    public ArrayCell() { }
    public static _IArrayCell<T> Default() {
      return create_Unset();
    }
    public static Dafny.TypeDescriptor<Dafny._IArrayCell<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Dafny._IArrayCell<T>>(Dafny.ArrayCell<T>.Default());
    }
    public static _IArrayCell<T> create_Set(T @value) {
      return new ArrayCell_Set<T>(@value);
    }
    public static _IArrayCell<T> create_Unset() {
      return new ArrayCell_Unset<T>();
    }
    public bool is_Set { get { return this is ArrayCell_Set<T>; } }
    public bool is_Unset { get { return this is ArrayCell_Unset<T>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((ArrayCell_Set<T>)d).@value;
      }
    }
    public abstract _IArrayCell<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public class ArrayCell_Set<T> : ArrayCell<T> {
    public readonly T @value;
    public ArrayCell_Set(T @value) {
      this.@value = @value;
    }
    public override _IArrayCell<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IArrayCell<__T> dt) { return dt; }
      return new ArrayCell_Set<__T>(converter0(@value));
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.ArrayCell_Set<T>;
      return oth != null && object.Equals(this.@value, oth.@value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny_Compile.ArrayCell.Set";
      s += "(";
      s += Dafny.Helpers.ToString(this.@value);
      s += ")";
      return s;
    }
  }
  public class ArrayCell_Unset<T> : ArrayCell<T> {
    public ArrayCell_Unset() {
    }
    public override _IArrayCell<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IArrayCell<__T> dt) { return dt; }
      return new ArrayCell_Unset<__T>();
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.ArrayCell_Unset<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny_Compile.ArrayCell.Unset";
      return s;
    }
  }

  public interface ImmutableArray<out T> {
    BigInteger Length();
    T Select(BigInteger index);
    Dafny.ImmutableArray<T> Subarray(BigInteger lo, BigInteger hi);
  }
  public class _Companion_ImmutableArray<T> {
  }

  public partial class Vector<T> : Dafny.Validatable {
    public Vector() {
      this.storage = default(Dafny.Array<T>);
      this.size = BigInteger.Zero;
    }
    public  Dafny.Array<T> storage {get; set;}
    public  BigInteger size {get; set;}
    public void __ctor(BigInteger length)
    {
      Dafny.Array<T> _0_storage;
      Dafny.Array<T> _out0;
      _out0 = Dafny.__default.NewArray<T>(length);
      _0_storage = _out0;
      (this).storage = _0_storage;
      (this).size = BigInteger.Zero;
    }
    public T Select(BigInteger index) {
      return (this.storage).Select(index);
    }
    public T Last() {
      return (this.storage).Select((this.size) - (BigInteger.One));
    }
    public void AddLast(T t)
    {
      if ((this.size) == ((this.storage).Length())) {
        (this).Reallocate((this).Max((this).MIN__SIZE, ((this.storage).Length()) * (new BigInteger(2))));
      }
      (this.storage).Update(this.size, t);
      (this).size = (this.size) + (BigInteger.One);
    }
    public BigInteger Max(BigInteger a, BigInteger b)
    {
      if ((a) < (b)) {
        return b;
      } else {
        return a;
      }
    }
    public void Reallocate(BigInteger newCapacity)
    {
      Dafny.Array<T> _1_newStorage;
      Dafny.Array<T> _out1;
      _out1 = Dafny.__default.NewArray<T>(newCapacity);
      _1_newStorage = _out1;
      Dafny.ImmutableArray<T> _2_values;
      Dafny.ImmutableArray<T> _out2;
      _out2 = (this.storage).Freeze(this.size);
      _2_values = _out2;
      (_1_newStorage).UpdateSubarray(BigInteger.Zero, _2_values);
      (this).storage = _1_newStorage;
    }
    public T RemoveLast()
    {
      T t = default(T);
      t = (this.storage).Select((this.size) - (BigInteger.One));
      (this).size = (this.size) - (BigInteger.One);
      return t;
    }
    public void Append(Dafny.ImmutableArray<T> other)
    {
      BigInteger _3_newSize;
      _3_newSize = (this.size) + ((other).Length());
      if (((this.storage).Length()) < (_3_newSize)) {
        (this).Reallocate((this).Max(_3_newSize, ((this.storage).Length()) * (new BigInteger(2))));
      }
      (this.storage).UpdateSubarray(this.size, other);
      (this).size = (this.size) + ((other).Length());
    }
    public Dafny.ImmutableArray<T> Freeze()
    {
      Dafny.ImmutableArray<T> ret = default(Dafny.ImmutableArray<T>);
      Dafny.ImmutableArray<T> _out3;
      _out3 = (this.storage).Freeze(this.size);
      ret = _out3;
      return ret;
    }
    public BigInteger MIN__SIZE { get {
      return new BigInteger(10);
    } }
  }


  public interface Sequence<out T> {
    BigInteger Length();
    uint HashCode();
    Dafny.ISequence<char> _ToString();
    T Select(BigInteger index);
    Dafny.Sequence<T> Drop(BigInteger lo);
    Dafny.Sequence<T> Take(BigInteger hi);
    Dafny.Sequence<T> Subsequence(BigInteger lo, BigInteger hi);
    Dafny.ImmutableArray<T> ToArray();
  }
  public class _Companion_Sequence<T> {
    public static uint HashCode(Dafny.Sequence<T> _this)
    {
      uint ret = 0;
      ret = 0U;
      BigInteger _hi0 = (_this).Length();
      for (BigInteger _4_i = BigInteger.Zero; _4_i < _hi0; _4_i++) {
        T _5_element;
        T _out4;
        _out4 = (_this).Select(_4_i);
        _5_element = _out4;
        ret = ((unchecked((uint)(((ret) << (int)(new BigInteger(3)))))) | ((ret) >> (int)(new BigInteger(29)))) ^ (Helpers_Compile.__default.HashCode<T>(_5_element));
      }
      return ret;
    }
    public static Dafny.ISequence<char> _ToString(Dafny.Sequence<T> _this)
    {
      Dafny.ISequence<char> ret = Dafny.Sequence<char>.Empty;
      ret = Dafny.Sequence<char>.FromString("[");
      BigInteger _hi1 = (_this).Length();
      for (BigInteger _6_i = BigInteger.Zero; _6_i < _hi1; _6_i++) {
        if ((_6_i).Sign != 0) {
          ret = Dafny.Sequence<char>.Concat(ret, Dafny.Sequence<char>.FromString(","));
        }
        T _7_element;
        T _out5;
        _out5 = (_this).Select(_6_i);
        _7_element = _out5;
        ret = Dafny.Sequence<char>.Concat(ret, Helpers_Compile.__default._ToString<T>(_7_element));
      }
      ret = Dafny.Sequence<char>.Concat(ret, Dafny.Sequence<char>.FromString("]"));
      return ret;
    }
    public static T Select(Dafny.Sequence<T> _this, BigInteger index)
    {
      T ret = default(T);
      Dafny.ImmutableArray<T> _8_a;
      Dafny.ImmutableArray<T> _out6;
      _out6 = (_this).ToArray();
      _8_a = _out6;
      ret = (_8_a).Select(index);
      return ret;
      return ret;
    }
    public static Dafny.Sequence<T> Drop(Dafny.Sequence<T> _this, BigInteger lo)
    {
      Dafny.Sequence<T> ret = default(Dafny.Sequence<T>);
      Dafny.Sequence<T> _out7;
      _out7 = (_this).Subsequence(lo, (_this).Length());
      ret = _out7;
      return ret;
    }
    public static Dafny.Sequence<T> Take(Dafny.Sequence<T> _this, BigInteger hi)
    {
      Dafny.Sequence<T> ret = default(Dafny.Sequence<T>);
      Dafny.Sequence<T> _out8;
      _out8 = (_this).Subsequence(BigInteger.Zero, hi);
      ret = _out8;
      return ret;
    }
    public static Dafny.Sequence<T> Subsequence(Dafny.Sequence<T> _this, BigInteger lo, BigInteger hi)
    {
      Dafny.Sequence<T> ret = default(Dafny.Sequence<T>);
      Dafny.ImmutableArray<T> _9_a;
      Dafny.ImmutableArray<T> _out9;
      _out9 = (_this).ToArray();
      _9_a = _out9;
      Dafny.ImmutableArray<T> _10_subarray;
      Dafny.ImmutableArray<T> _out10;
      _out10 = (_9_a).Subarray(lo, hi);
      _10_subarray = _out10;
      Dafny.ArraySequence<T> _nw0 = new Dafny.ArraySequence<T>();
      _nw0.__ctor(_10_subarray);
      ret = _nw0;
      return ret;
    }
  }

  public partial class ArraySequence<T> : Dafny.Sequence<T> {
    public ArraySequence() {
      this._value = default(Dafny.ImmutableArray<T>);
    }
    public uint HashCode()
    {
      uint _out11;
      _out11 = Dafny._Companion_Sequence<T>.HashCode(this);
      return _out11;
    }
    public Dafny.ISequence<char> _ToString()
    {
      Dafny.ISequence<char> _out12;
      _out12 = Dafny._Companion_Sequence<T>._ToString(this);
      return _out12;
    }
    public T Select(BigInteger index)
    {
      T _out13;
      _out13 = Dafny._Companion_Sequence<T>.Select(this, index);
      return _out13;
    }
    public Dafny.Sequence<T> Drop(BigInteger lo)
    {
      Dafny.Sequence<T> _out14;
      _out14 = Dafny._Companion_Sequence<T>.Drop(this, lo);
      return _out14;
    }
    public Dafny.Sequence<T> Take(BigInteger hi)
    {
      Dafny.Sequence<T> _out15;
      _out15 = Dafny._Companion_Sequence<T>.Take(this, hi);
      return _out15;
    }
    public Dafny.Sequence<T> Subsequence(BigInteger lo, BigInteger hi)
    {
      Dafny.Sequence<T> _out16;
      _out16 = Dafny._Companion_Sequence<T>.Subsequence(this, lo, hi);
      return _out16;
    }
    public void __ctor(Dafny.ImmutableArray<T> @value)
    {
      (this)._value = @value;
    }
    public BigInteger Length() {
      return ((this).@value).Length();
    }
    public Dafny.ImmutableArray<T> ToArray()
    {
      Dafny.ImmutableArray<T> ret = default(Dafny.ImmutableArray<T>);
      ret = (this).@value;
      return ret;
      return ret;
    }
    public  Dafny.ImmutableArray<T> _value {get; set;}
    public Dafny.ImmutableArray<T> @value { get {
      return this._value;
    } }
  }

  public partial class ConcatSequence<T> : Dafny.Sequence<T> {
    public ConcatSequence() {
      this._left = default(Dafny.Sequence<T>);
      this._right = default(Dafny.Sequence<T>);
      this._length = BigInteger.Zero;
    }
    public uint HashCode()
    {
      uint _out17;
      _out17 = Dafny._Companion_Sequence<T>.HashCode(this);
      return _out17;
    }
    public Dafny.ISequence<char> _ToString()
    {
      Dafny.ISequence<char> _out18;
      _out18 = Dafny._Companion_Sequence<T>._ToString(this);
      return _out18;
    }
    public T Select(BigInteger index)
    {
      T _out19;
      _out19 = Dafny._Companion_Sequence<T>.Select(this, index);
      return _out19;
    }
    public Dafny.Sequence<T> Drop(BigInteger lo)
    {
      Dafny.Sequence<T> _out20;
      _out20 = Dafny._Companion_Sequence<T>.Drop(this, lo);
      return _out20;
    }
    public Dafny.Sequence<T> Take(BigInteger hi)
    {
      Dafny.Sequence<T> _out21;
      _out21 = Dafny._Companion_Sequence<T>.Take(this, hi);
      return _out21;
    }
    public Dafny.Sequence<T> Subsequence(BigInteger lo, BigInteger hi)
    {
      Dafny.Sequence<T> _out22;
      _out22 = Dafny._Companion_Sequence<T>.Subsequence(this, lo, hi);
      return _out22;
    }
    public void __ctor(Dafny.Sequence<T> left, Dafny.Sequence<T> right)
    {
      (this)._left = left;
      (this)._right = right;
      (this)._length = ((left).Length()) + ((right).Length());
    }
    public BigInteger Length() {
      return (this).length;
    }
    public Dafny.ImmutableArray<T> ToArray()
    {
      Dafny.ImmutableArray<T> ret = default(Dafny.ImmutableArray<T>);
      Dafny.Vector<T> _11_builder;
      Dafny.Vector<T> _nw1 = new Dafny.Vector<T>();
      _nw1.__ctor((this).length);
      _11_builder = _nw1;
      Dafny.Vector<Dafny.Sequence<T>> _12_stack;
      Dafny.Vector<Dafny.Sequence<T>> _nw2 = new Dafny.Vector<Dafny.Sequence<T>>();
      _nw2.__ctor(new BigInteger(10));
      _12_stack = _nw2;
      Dafny.__default.AppendOptimized<T>(_11_builder, this, _12_stack);
      Dafny.ImmutableArray<T> _out23;
      _out23 = (_11_builder).Freeze();
      ret = _out23;
      return ret;
    }
    public  Dafny.Sequence<T> _left {get; set;}
    public Dafny.Sequence<T> left { get {
      return this._left;
    } }
    public  Dafny.Sequence<T> _right {get; set;}
    public Dafny.Sequence<T> right { get {
      return this._right;
    } }
    public  BigInteger _length {get; set;}
    public BigInteger length { get {
      return this._length;
    } }
  }

  public partial class LazySequence<T> : Dafny.Sequence<T> {
    public LazySequence() {
      this._length = BigInteger.Zero;
      this._box = default(Dafny.AtomicBox<Dafny.Sequence<T>>);
    }
    public uint HashCode()
    {
      uint _out24;
      _out24 = Dafny._Companion_Sequence<T>.HashCode(this);
      return _out24;
    }
    public Dafny.ISequence<char> _ToString()
    {
      Dafny.ISequence<char> _out25;
      _out25 = Dafny._Companion_Sequence<T>._ToString(this);
      return _out25;
    }
    public T Select(BigInteger index)
    {
      T _out26;
      _out26 = Dafny._Companion_Sequence<T>.Select(this, index);
      return _out26;
    }
    public Dafny.Sequence<T> Drop(BigInteger lo)
    {
      Dafny.Sequence<T> _out27;
      _out27 = Dafny._Companion_Sequence<T>.Drop(this, lo);
      return _out27;
    }
    public Dafny.Sequence<T> Take(BigInteger hi)
    {
      Dafny.Sequence<T> _out28;
      _out28 = Dafny._Companion_Sequence<T>.Take(this, hi);
      return _out28;
    }
    public Dafny.Sequence<T> Subsequence(BigInteger lo, BigInteger hi)
    {
      Dafny.Sequence<T> _out29;
      _out29 = Dafny._Companion_Sequence<T>.Subsequence(this, lo, hi);
      return _out29;
    }
    public void __ctor(Dafny.Sequence<T> wrapped)
    {
      Dafny.AtomicBox<Dafny.Sequence<T>> _13_box;
      Dafny.AtomicBox<Dafny.Sequence<T>> _out30;
      _out30 = Dafny.AtomicBox<Dafny.Sequence<T>>.Make(wrapped);
      _13_box = _out30;
      (this)._box = _13_box;
      (this)._length = (wrapped).Length();
    }
    public BigInteger Length() {
      return (this).length;
    }
    public Dafny.ImmutableArray<T> ToArray()
    {
      Dafny.ImmutableArray<T> ret = default(Dafny.ImmutableArray<T>);
      Dafny.Sequence<T> _14_expr;
      Dafny.Sequence<T> _out31;
      _out31 = ((this).box).Get();
      _14_expr = _out31;
      Dafny.ImmutableArray<T> _out32;
      _out32 = (_14_expr).ToArray();
      ret = _out32;
      Dafny.ArraySequence<T> _15_arraySeq;
      Dafny.ArraySequence<T> _nw3 = new Dafny.ArraySequence<T>();
      _nw3.__ctor(ret);
      _15_arraySeq = _nw3;
      ((this).box).Put(_15_arraySeq);
      return ret;
    }
    public  BigInteger _length {get; set;}
    public BigInteger length { get {
      return this._length;
    } }
    public  Dafny.AtomicBox<Dafny.Sequence<T>> _box {get; set;}
    public Dafny.AtomicBox<Dafny.Sequence<T>> box { get {
      return this._box;
    } }
  }

  public partial class __default {
    public static void AppendRecursive<__T>(Dafny.Vector<__T> builder, Dafny.Sequence<__T> e)
    {
      if (Dafny.Helpers.Let<Dafny.Sequence<__T>, bool>(e, _is_0 => _is_0 is Dafny.ConcatSequence<__T>)) {
        Dafny.ConcatSequence<__T> _16_concat;
        _16_concat = ((Dafny.ConcatSequence<__T>)(e));
        Dafny.__default.AppendRecursive<__T>(builder, (_16_concat).left);
        Dafny.__default.AppendRecursive<__T>(builder, (_16_concat).right);
      } else if (Dafny.Helpers.Let<Dafny.Sequence<__T>, bool>(e, _is_1 => _is_1 is Dafny.LazySequence<__T>)) {
        Dafny.LazySequence<__T> _17_lazy;
        _17_lazy = ((Dafny.LazySequence<__T>)(e));
        Dafny.Sequence<__T> _18_boxed;
        Dafny.Sequence<__T> _out33;
        _out33 = ((_17_lazy).box).Get();
        _18_boxed = _out33;
        Dafny.__default.AppendRecursive<__T>(builder, _18_boxed);
      } else {
        Dafny.ImmutableArray<__T> _19_a;
        Dafny.ImmutableArray<__T> _out34;
        _out34 = (e).ToArray();
        _19_a = _out34;
        (builder).Append(_19_a);
      }
    }
    public static void AppendOptimized<__T>(Dafny.Vector<__T> builder, Dafny.Sequence<__T> e, Dafny.Vector<Dafny.Sequence<__T>> stack)
    {
    TAIL_CALL_START: ;
      if (Dafny.Helpers.Let<Dafny.Sequence<__T>, bool>(e, _is_2 => _is_2 is Dafny.ConcatSequence<__T>)) {
        Dafny.ConcatSequence<__T> _20_concat;
        _20_concat = ((Dafny.ConcatSequence<__T>)(e));
        (stack).AddLast((_20_concat).right);
        Dafny.Vector<__T> _in0 = builder;
        Dafny.Sequence<__T> _in1 = (_20_concat).left;
        Dafny.Vector<Dafny.Sequence<__T>> _in2 = stack;
        builder = _in0;
        e = _in1;
        stack = _in2;
        goto TAIL_CALL_START;
      } else if (Dafny.Helpers.Let<Dafny.Sequence<__T>, bool>(e, _is_3 => _is_3 is Dafny.LazySequence<__T>)) {
        Dafny.LazySequence<__T> _21_lazy;
        _21_lazy = ((Dafny.LazySequence<__T>)(e));
        Dafny.Sequence<__T> _22_boxed;
        Dafny.Sequence<__T> _out35;
        _out35 = ((_21_lazy).box).Get();
        _22_boxed = _out35;
        Dafny.Vector<__T> _in3 = builder;
        Dafny.Sequence<__T> _in4 = _22_boxed;
        Dafny.Vector<Dafny.Sequence<__T>> _in5 = stack;
        builder = _in3;
        e = _in4;
        stack = _in5;
        goto TAIL_CALL_START;
      } else if (Dafny.Helpers.Let<Dafny.Sequence<__T>, bool>(e, _is_4 => _is_4 is Dafny.ArraySequence<__T>)) {
        Dafny.ArraySequence<__T> _23_a;
        _23_a = ((Dafny.ArraySequence<__T>)(e));
        (builder).Append((_23_a).@value);
        if ((stack.size).Sign == 1) {
          Dafny.Sequence<__T> _24_next;
          Dafny.Sequence<__T> _out36;
          _out36 = (stack).RemoveLast();
          _24_next = _out36;
          Dafny.Vector<__T> _in6 = builder;
          Dafny.Sequence<__T> _in7 = _24_next;
          Dafny.Vector<Dafny.Sequence<__T>> _in8 = stack;
          builder = _in6;
          e = _in7;
          stack = _in8;
          goto TAIL_CALL_START;
        }
      } else {
      }
    }
    public static bool EqualUpTo<__T>(Dafny.Sequence<__T> left, Dafny.Sequence<__T> right, BigInteger index)
    {
      bool ret = false;
      BigInteger _hi2 = index;
      for (BigInteger _25_i = BigInteger.Zero; _25_i < _hi2; _25_i++) {
        __T _26_leftElement;
        __T _out37;
        _out37 = (left).Select(_25_i);
        _26_leftElement = _out37;
        __T _27_rightElement;
        __T _out38;
        _out38 = (right).Select(_25_i);
        _27_rightElement = _out38;
        if (!object.Equals(_26_leftElement, _27_rightElement)) {
          ret = false;
          return ret;
        }
      }
      ret = true;
      return ret;
      return ret;
    }
    public static bool EqualSequences<__T>(Dafny.Sequence<__T> left, Dafny.Sequence<__T> right)
    {
      bool ret = false;
      if (((left).Length()) != ((right).Length())) {
        ret = false;
        return ret;
      }
      bool _out39;
      _out39 = Dafny.__default.EqualUpTo<__T>(left, right, (left).Length());
      ret = _out39;
      return ret;
    }
    public static bool IsPrefixOf<__T>(Dafny.Sequence<__T> left, Dafny.Sequence<__T> right)
    {
      bool ret = false;
      if (((right).Length()) < ((left).Length())) {
        ret = false;
        return ret;
      }
      bool _out40;
      _out40 = Dafny.__default.EqualUpTo<__T>(left, right, (left).Length());
      ret = _out40;
      return ret;
    }
    public static bool IsProperPrefixOf<__T>(Dafny.Sequence<__T> left, Dafny.Sequence<__T> right)
    {
      bool ret = false;
      if (((right).Length()) <= ((left).Length())) {
        ret = false;
        return ret;
      }
      bool _out41;
      _out41 = Dafny.__default.EqualUpTo<__T>(left, right, (left).Length());
      ret = _out41;
      return ret;
    }
    public static bool Contains<__T>(Dafny.Sequence<__T> s, __T t)
    {
      bool _hresult = false;
      BigInteger _hi3 = (s).Length();
      for (BigInteger _28_i = BigInteger.Zero; _28_i < _hi3; _28_i++) {
        __T _29_element;
        __T _out42;
        _out42 = (s).Select(_28_i);
        _29_element = _out42;
        if (object.Equals(_29_element, t)) {
          _hresult = true;
          return _hresult;
        }
      }
      _hresult = false;
      return _hresult;
      return _hresult;
    }
    public static Dafny.Sequence<__T> Concatenate<__T>(Dafny.Sequence<__T> left, Dafny.Sequence<__T> right)
    {
      Dafny.Sequence<__T> ret = default(Dafny.Sequence<__T>);
      Dafny.ConcatSequence<__T> _30_c;
      Dafny.ConcatSequence<__T> _nw4 = new Dafny.ConcatSequence<__T>();
      _nw4.__ctor(left, right);
      _30_c = _nw4;
      Dafny.LazySequence<__T> _nw5 = new Dafny.LazySequence<__T>();
      _nw5.__ctor(_30_c);
      ret = _nw5;
      return ret;
    }
    public static Dafny.Sequence<__T> Update<__T>(Dafny.Sequence<__T> s, BigInteger i, __T t)
    {
      Dafny.Sequence<__T> ret = default(Dafny.Sequence<__T>);
      Dafny.ImmutableArray<__T> _31_a;
      Dafny.ImmutableArray<__T> _out43;
      _out43 = (s).ToArray();
      _31_a = _out43;
      Dafny.Array<__T> _32_newValue;
      Dafny.Array<__T> _out44;
      _out44 = Dafny.__default.CopyArray<__T>(_31_a);
      _32_newValue = _out44;
      (_32_newValue).Update(i, t);
      Dafny.ImmutableArray<__T> _33_newValueFrozen;
      Dafny.ImmutableArray<__T> _out45;
      _out45 = (_32_newValue).Freeze((_32_newValue).Length());
      _33_newValueFrozen = _out45;
      Dafny.ArraySequence<__T> _nw6 = new Dafny.ArraySequence<__T>();
      _nw6.__ctor(_33_newValueFrozen);
      ret = _nw6;
      return ret;
    }
    public static void MultiDimentionalArrays()
    {
      BigInteger[,,] _34_a;
      BigInteger[,,] _nw7 = new BigInteger[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(new BigInteger(3), "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int"), Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(new BigInteger(4), "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int"), Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(new BigInteger(5), "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      Func<BigInteger, BigInteger, BigInteger, BigInteger> _arrayinit0 = ((System.Func<BigInteger, BigInteger, BigInteger, BigInteger>)((_35_i, _36_j, _37_k) => {
        return BigInteger.Zero;
      }));
      for (var _arrayinit_00 = 0; _arrayinit_00 < new BigInteger(_nw7.GetLength(0)); _arrayinit_00++) {
        for (var _arrayinit_10 = 0; _arrayinit_10 < new BigInteger(_nw7.GetLength(1)); _arrayinit_10++) {
          for (var _arrayinit_20 = 0; _arrayinit_20 < new BigInteger(_nw7.GetLength(2)); _arrayinit_20++) {
            _nw7[(int)(_arrayinit_00), (int)(_arrayinit_10), (int)(_arrayinit_20)] = _arrayinit0(_arrayinit_00, _arrayinit_10, _arrayinit_20);
          }
        }
      }
      _34_a = _nw7;
      (_34_a)[(int)((BigInteger.One)), (int)((BigInteger.One)), (int)((BigInteger.One))] = new BigInteger(42);
    }
  }
} // end of namespace Dafny
namespace _module {

} // end of namespace _module
