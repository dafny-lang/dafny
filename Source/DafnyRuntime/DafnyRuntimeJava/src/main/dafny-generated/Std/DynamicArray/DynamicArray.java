// Class DynamicArray
// Dafny class DynamicArray compiled into Java
package Std.DynamicArray;

import JavaInternal.*;
import Std.Wrappers.*;
import Std.FileIOInternalExterns.*;
import Std.BoundedInts.*;
import Std.Base64.*;
import Std.Math.*;
import Std.Collections.Seq.*;
import Std.Collections.Array.*;
import Std.Collections.Imap.*;
import Std.Collections.Map.*;
import Std.Collections.Set.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class DynamicArray<A> {
  protected dafny.TypeDescriptor<A> _td_A;
  public DynamicArray(dafny.TypeDescriptor<A> _td_A) {
    this._td_A = _td_A;
    this.size = java.math.BigInteger.ZERO;
    this.capacity = java.math.BigInteger.ZERO;
    this.data = (java.lang.Object)_td_A.newArray(0);
  }
  public java.math.BigInteger size;
  public java.math.BigInteger capacity;
  public java.lang.Object data;
  public void __ctor()
  {
    (this).size = java.math.BigInteger.ZERO;
    (this).capacity = java.math.BigInteger.ZERO;
    java.lang.Object _nw3 = (java.lang.Object) _td_A.newArray(dafny.Helpers.toIntChecked((java.math.BigInteger.ZERO), "Java arrays may be no larger than the maximum 32-bit signed int"));
    (this).data = _nw3;
  }
  public A At(java.math.BigInteger index) {
    return _td_A.getArrayElement((this.data), (dafny.Helpers.toInt((index))));
  }
  public void Put(java.math.BigInteger index, A element)
  {
    java.lang.Object _arr0 = this.data;
    _td_A.setArrayElement(_arr0, dafny.Helpers.toInt(((index)).intValue()), element);
  }
  public void Ensure(java.math.BigInteger reserved, A defaultValue)
  {
    java.math.BigInteger _135_newCapacity = java.math.BigInteger.ZERO;
    _135_newCapacity = this.capacity;
    while ((reserved).compareTo((_135_newCapacity).subtract(this.size)) > 0) {
      _135_newCapacity = (this).DefaultNewCapacity(_135_newCapacity);
    }
    if ((_135_newCapacity).compareTo(this.capacity) > 0) {
      (this).Realloc(defaultValue, _135_newCapacity);
    }
  }
  public void PopFast()
  {
    (this).size = (this.size).subtract(java.math.BigInteger.ONE);
  }
  public void PushFast(A element)
  {
    java.lang.Object _arr1 = this.data;
    java.math.BigInteger _index5 = this.size;
    _td_A.setArrayElement(_arr1, dafny.Helpers.toInt((_index5).intValue()), element);
    (this).size = (this.size).add(java.math.BigInteger.ONE);
  }
  public void Push(A element)
  {
    if (java.util.Objects.equals(this.size, this.capacity)) {
      (this).ReallocDefault(element);
    }
    (this).PushFast(element);
  }
  public void Realloc(A defaultValue, java.math.BigInteger newCapacity)
  {
    java.lang.Object _136_oldData;
    java.math.BigInteger _137_oldCapacity = java.math.BigInteger.ZERO;
    java.lang.Object _rhs7 = this.data;
    java.math.BigInteger _rhs8 = this.capacity;
    _136_oldData = _rhs7;
    _137_oldCapacity = _rhs8;
    java.util.function.Function<java.math.BigInteger, A> _init3 = ((java.util.function.Function<A, java.util.function.Function<java.math.BigInteger, A>>)(_138_defaultValue) -> ((java.util.function.Function<java.math.BigInteger, A>)(_139___v0_boxed0) -> {
      java.math.BigInteger _139___v0 = ((java.math.BigInteger)(java.lang.Object)(_139___v0_boxed0));
      return _138_defaultValue;
    })).apply(defaultValue);
    java.lang.Object _nw4 = (java.lang.Object) _td_A.newArray(dafny.Helpers.toIntChecked((newCapacity), "Java arrays may be no larger than the maximum 32-bit signed int"));
    for (java.math.BigInteger _i0_3 = java.math.BigInteger.ZERO; _i0_3.compareTo(java.math.BigInteger.valueOf(java.lang.reflect.Array.getLength(_nw4))) < 0; _i0_3 = _i0_3.add(java.math.BigInteger.ONE)) {
      _td_A.setArrayElement(_nw4, dafny.Helpers.toInt(_i0_3), ((A)(java.lang.Object)(_init3.apply(_i0_3))));
    }
    java.lang.Object _rhs9 = _nw4;
    java.math.BigInteger _rhs10 = newCapacity;
    DynamicArray<A> _lhs0 = this;
    DynamicArray<A> _lhs1 = this;
    _lhs0.data = _rhs9;
    _lhs1.capacity = _rhs10;
    (this).CopyFrom(_136_oldData, _137_oldCapacity);
  }
  public java.math.BigInteger DefaultNewCapacity(java.math.BigInteger capacity) {
    if ((capacity).signum() == 0) {
      return java.math.BigInteger.valueOf(8L);
    } else {
      return (java.math.BigInteger.valueOf(2L)).multiply(capacity);
    }
  }
  public void ReallocDefault(A defaultValue)
  {
    (this).Realloc(defaultValue, (this).DefaultNewCapacity(this.capacity));
  }
  public void CopyFrom(java.lang.Object newData, java.math.BigInteger count)
  {
    for (java.math.BigInteger _guard_loop_0_boxed0 : dafny.Helpers.IntegerRange(java.math.BigInteger.ZERO, count)) {
      java.math.BigInteger _guard_loop_0 = ((java.math.BigInteger)(java.lang.Object)(_guard_loop_0_boxed0));
      if (true) {
        java.math.BigInteger _140_index = (java.math.BigInteger)_guard_loop_0;
        if ((true) && (((_140_index).signum() != -1) && ((_140_index).compareTo(count) < 0))) {
          java.lang.Object _arr2 = this.data;
          _td_A.setArrayElement(_arr2, dafny.Helpers.toInt(((_140_index)).intValue()), _td_A.getArrayElement((newData), (dafny.Helpers.toInt((_140_index)))));
        }
      }
    }
  }
  @Override
  public java.lang.String toString() {
    return "Std.DynamicArray.DynamicArray";
  }
}
