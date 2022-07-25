// Dafny program array.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// Dafny 3.7.2.40713
// Command Line Options: /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/array.dfy /compileTarget:cs /out:../DafnyRuntime/generated
// array.dfy


module {:extern ""Arrays""} {:options ""/functionSyntax:4""} Arrays {

  import opened Frames
  trait {:extern} {:termination false} Array<T> extends Validatable {
    ghost var values: seq<ArrayCell<T>>

    function method Length(): nat
      requires Valid()
      reads Repr
      ensures Length() == |values|
      decreases Repr

    function method Read(i: nat): (ret: T)
      requires Valid()
      requires i < Length()
      requires values[i].Set?
      reads this, Repr
      ensures ret == values[i].value
      decreases Repr + {this}, i

    method Write(i: nat, t: T)
      requires Valid()
      requires i < Length()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures values == old(values)[..i] + [Set(t)] + old(values)[i + 1..]
      ensures Read(i) == t
      decreases i

    method WriteRangeArray(start: nat, other: ImmutableArray<T>)
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

  trait {:extern} {:termination false} ImmutableArray<+T> {
    ghost const values: seq<T>

    predicate Valid()

    function CellValues(): seq<ArrayCell<T>>
    {
      seq(|values|, (i: int) requires 0 <= i < |values| => Set(values[i]))
    }

    function method Length(): nat
      requires Valid()
      ensures Length() == |values|

    function method At(index: nat): T
      requires Valid()
      requires index < |values|
      ensures At(index) == values[index]
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
      decreases Repr + {this}
    {
      this in Repr &&
      ValidComponent(storage) &&
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
      seq(size, (i: int) requires 0 <= i < size && Valid() reads this, Repr => storage.Read(i))
    }

    function method At(index: nat): T
      requires Valid()
      requires index < size
      reads this, Repr
      ensures At(index) == Value()[index]
      decreases Repr + {this}, index
    {
      storage.Read(index)
    }

    function method Last(): T
      requires Valid()
      requires 0 < size
      reads this, Repr
      ensures Last() == Value()[size - 1]
      decreases Repr + {this}
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
      ensures Value() == old(Value()[..size - 1])
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
      decreases other
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
    {
      ret := storage.Freeze(size);
    }
  }

  method {:extern} NewArray<T>(length: nat) returns (ret: Array<T>)
    ensures ret.Valid()
    ensures fresh(ret.Repr)
    ensures ret.Length() == length
    decreases length
}

module {:options ""/functionSyntax:4""} Frames {
  trait {:termination false} Validatable {
    ghost var Repr: set<object>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}

    predicate ValidComponent(component: Validatable)
      reads this, Repr
      decreases Repr + {this}, component
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

  predicate PairwiseDisjoint(s: set<Validatable>)
    reads s, set v: Validatable, o: object {:trigger o in v.Repr} | v in s && o in v.Repr :: o
    decreases s + set v: Validatable, o: object {:trigger o in v.Repr} | v in s && o in v.Repr :: o, s
  {
    true &&
    forall v: Validatable | v in s :: 
      v.Valid() &&
      forall v: Validatable, v': Validatable | v in s && v' in s && v != v' :: 
        v.Repr !! v'.Repr
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
}
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace _System
namespace Frames_Compile {

  public interface Validatable {
  }
  public class _Companion_Validatable {
  }

} // end of namespace Frames_Compile
namespace Arrays {

  public interface Array<T> : Frames_Compile.Validatable {
    BigInteger Length();
    T Read(BigInteger i);
    void Write(BigInteger i, T t);
    void WriteRangeArray(BigInteger start, Arrays.ImmutableArray<T> other);
    Arrays.ImmutableArray<T> Freeze(BigInteger size);
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
    public static Dafny.TypeDescriptor<Arrays._IArrayCell<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Arrays._IArrayCell<T>>(Arrays.ArrayCell<T>.Default());
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
      var oth = other as Arrays.ArrayCell_Set<T>;
      return oth != null && object.Equals(this.@value, oth.@value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Arrays_Compile.ArrayCell.Set";
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
      var oth = other as Arrays.ArrayCell_Unset<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Arrays_Compile.ArrayCell.Unset";
      return s;
    }
  }

  public interface ImmutableArray<out T> {
    BigInteger Length();
    T At(BigInteger index);
    Arrays.ImmutableArray<T> Subarray(BigInteger lo, BigInteger hi);
  }
  public class _Companion_ImmutableArray<T> {
  }

  public partial class Vector<T> : Frames_Compile.Validatable {
    public Vector() {
      this.storage = default(Arrays.Array<T>);
      this.size = BigInteger.Zero;
    }
    public  Arrays.Array<T> storage {get; set;}
    public  BigInteger size {get; set;}
    public void __ctor(BigInteger length)
    {
      Arrays.Array<T> _0_storage;
      Arrays.Array<T> _out0;
      _out0 = Arrays.__default.NewArray<T>(length);
      _0_storage = _out0;
      (this).storage = _0_storage;
      (this).size = BigInteger.Zero;
    }
    public T At(BigInteger index) {
      return (this.storage).Read(index);
    }
    public T Last() {
      return (this.storage).Read((this.size) - (BigInteger.One));
    }
    public void AddLast(T t)
    {
      if ((this.size) == ((this.storage).Length())) {
        (this).Reallocate((this).Max((this).MIN__SIZE, ((this.storage).Length()) * (new BigInteger(2))));
      }
      (this.storage).Write(this.size, t);
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
      Arrays.Array<T> _1_newStorage;
      Arrays.Array<T> _out1;
      _out1 = Arrays.__default.NewArray<T>(newCapacity);
      _1_newStorage = _out1;
      Arrays.ImmutableArray<T> _2_values;
      Arrays.ImmutableArray<T> _out2;
      _out2 = (this.storage).Freeze(this.size);
      _2_values = _out2;
      (_1_newStorage).WriteRangeArray(BigInteger.Zero, _2_values);
      (this).storage = _1_newStorage;
    }
    public T RemoveLast()
    {
      T t = default(T);
      t = (this.storage).Read((this.size) - (BigInteger.One));
      (this).size = (this.size) - (BigInteger.One);
      return t;
    }
    public void Append(Arrays.ImmutableArray<T> other)
    {
      BigInteger _3_newSize;
      _3_newSize = (this.size) + ((other).Length());
      if (((this.storage).Length()) < (_3_newSize)) {
        (this).Reallocate((this).Max(_3_newSize, ((this.storage).Length()) * (new BigInteger(2))));
      }
      (this.storage).WriteRangeArray(this.size, other);
      (this).size = (this.size) + ((other).Length());
    }
    public Arrays.ImmutableArray<T> Freeze()
    {
      Arrays.ImmutableArray<T> ret = default(Arrays.ImmutableArray<T>);
      Arrays.ImmutableArray<T> _out3;
      _out3 = (this.storage).Freeze(this.size);
      ret = _out3;
      return ret;
    }
    public BigInteger MIN__SIZE { get {
      return new BigInteger(10);
    } }
  }

} // end of namespace Arrays
namespace _module {

} // end of namespace _module
