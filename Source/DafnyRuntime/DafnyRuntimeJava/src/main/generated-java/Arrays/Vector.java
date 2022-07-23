// Class Vector
// Dafny class Vector compiled into Java
package Arrays;

import Frames_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class Vector<T> implements Frames_Compile.Validatable {
  private dafny.TypeDescriptor<T> _td_T;
  public Vector(dafny.TypeDescriptor<T> _td_T) {
    this._td_T = _td_T;
    this.storage = null;
    this.size = java.math.BigInteger.ZERO;
  }
  public Array<T> storage;
  public java.math.BigInteger size;
  public void __ctor(java.math.BigInteger length)
  {
    Array<T> _0_storage;
    Array<T> _out0;
    _out0 = __default.<T>NewArray(_td_T, length);
    _0_storage = _out0;
    (this).storage = _0_storage;
    (this).size = java.math.BigInteger.ZERO;
  }
  public T At(java.math.BigInteger index) {
    return (this.storage).Read(index);
  }
  public T Last() {
    return (this.storage).Read((this.size).subtract((java.math.BigInteger.ONE)));
  }
  public void AddLast(T t)
  {
    if (java.util.Objects.equals(this.size, (this.storage).Length())) {
      (this).Reallocate((this).Max((this).MIN__SIZE(), ((this.storage).Length()).multiply((java.math.BigInteger.valueOf(2L)))));
    }
    (this.storage).Write(this.size, t);
    (this).size = (this.size).add((java.math.BigInteger.ONE));
  }
  public java.math.BigInteger Max(java.math.BigInteger a, java.math.BigInteger b)
  {
    if ((a).compareTo((b)) < 0) {
      return b;
    } else {
      return a;
    }
  }
  public void Reallocate(java.math.BigInteger newCapacity)
  {
    Array<T> _1_newStorage;
    Array<T> _out1;
    _out1 = __default.<T>NewArray(_td_T, newCapacity);
    _1_newStorage = _out1;
    ImmutableArray<T> _2_values;
    ImmutableArray<T> _out2;
    _out2 = (this.storage).Freeze(this.size);
    _2_values = _out2;
    (_1_newStorage).WriteRangeArray(java.math.BigInteger.ZERO, _2_values);
    (this).storage = _1_newStorage;
  }
  public T RemoveLast()
  {
    @SuppressWarnings({"unchecked", "deprecation"})
    T t = null;
    if(true) {
      t = (this.storage).Read((this.size).subtract((java.math.BigInteger.ONE)));
      (this).size = (this.size).subtract((java.math.BigInteger.ONE));
    }
    return t;
  }
  public void Append(ImmutableArray<T> other)
  {
    java.math.BigInteger _3_newSize = java.math.BigInteger.ZERO;
    _3_newSize = (this.size).add(((other).Length()));
    if (((this.storage).Length()).compareTo((_3_newSize)) < 0) {
      (this).Reallocate((this).Max(_3_newSize, ((this.storage).Length()).multiply((java.math.BigInteger.valueOf(2L)))));
    }
    (this.storage).WriteRangeArray(this.size, other);
    (this).size = (this.size).add(((other).Length()));
  }
  public ImmutableArray<T> Freeze()
  {
    ImmutableArray<T> ret = null;
    if(true) {
      ImmutableArray<T> _out3;
      _out3 = (this.storage).Freeze(this.size);
      ret = _out3;
    }
    return ret;
  }
  public java.math.BigInteger MIN__SIZE()
  {
    return java.math.BigInteger.valueOf(10L);
  }
  public static <T> dafny.TypeDescriptor<Vector<T>> _typeDescriptor(dafny.TypeDescriptor<T> _td_T) {
    return (dafny.TypeDescriptor<Vector<T>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.referenceWithInitializer(Vector.class, () -> (Vector<T>) null);
  }
}
