// Package Std_DynamicArray
// Dafny module Std_DynamicArray compiled into Go

package Std_DynamicArray

import (
  _dafny "dafny"
  os "os"
  _System "System_"
  Std_Wrappers "Std_Wrappers"
  Std_Concurrent "Std_Concurrent"
  Std_FileIOInternalExterns "Std_FileIOInternalExterns"
  Std_BoundedInts "Std_BoundedInts"
  Std_Base64 "Std_Base64"
  Std_Relations "Std_Relations"
  Std_Math "Std_Math"
  Std_Collections_Seq "Std_Collections_Seq"
  Std_Collections_Array "Std_Collections_Array"
  Std_Collections_Imap "Std_Collections_Imap"
  Std_Functions "Std_Functions"
  Std_Collections_Iset "Std_Collections_Iset"
  Std_Collections_Map "Std_Collections_Map"
  Std_Collections_Set "Std_Collections_Set"
  Std_Collections "Std_Collections"
)
var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Std_Wrappers.Dummy__
var _ Std_Concurrent.Dummy__
var _ = Std_FileIOInternalExterns.INTERNAL__ReadBytesFromFile
var _ Std_BoundedInts.Dummy__
var _ Std_Base64.Dummy__
var _ Std_Relations.Dummy__
var _ Std_Math.Dummy__
var _ Std_Collections_Seq.Dummy__
var _ Std_Collections_Array.Dummy__
var _ Std_Collections_Imap.Dummy__
var _ Std_Functions.Dummy__
var _ Std_Collections_Iset.Dummy__
var _ Std_Collections_Map.Dummy__
var _ Std_Collections_Set.Dummy__
var _ Std_Collections.Dummy__

type Dummy__ struct{}



// Definition of class DynamicArray
type DynamicArray struct {
  Size _dafny.Int
  Capacity _dafny.Int
  Data _dafny.Array
}

func New_DynamicArray_() *DynamicArray {
  _this := DynamicArray{}

  _this.Size = _dafny.Zero
  _this.Capacity = _dafny.Zero
  _this.Data = _dafny.NewArrayWithValue(nil, _dafny.IntOf(0))
  return &_this
}

type CompanionStruct_DynamicArray_ struct {
}
var Companion_DynamicArray_ = CompanionStruct_DynamicArray_ {
}

func (_this *DynamicArray) Equals(other *DynamicArray) bool {
  return _this == other
}

func (_this *DynamicArray) EqualsGeneric(x interface{}) bool {
  other, ok := x.(*DynamicArray)
  return ok && _this.Equals(other)
}

func (*DynamicArray) String() string {
  return "Std_DynamicArray.DynamicArray"
}

func Type_DynamicArray_(Type_A_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_DynamicArray_{Type_A_}
}

type type_DynamicArray_ struct {
  Type_A_ _dafny.TypeDescriptor
}

func (_this type_DynamicArray_) Default() interface{} {
  return (*DynamicArray)(nil)
}

func (_this type_DynamicArray_) String() string {
  return "Std_DynamicArray.DynamicArray"
}
func (_this *DynamicArray) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &DynamicArray{}

func (_this *DynamicArray) Ctor__() {
  {
    (_this).Size = _dafny.Zero
    (_this).Capacity = _dafny.Zero
    var _nw3 _dafny.Array = _dafny.NewArray(_dafny.Zero)
    _ = _nw3
    (_this).Data = _nw3
  }
}
func (_this *DynamicArray) At(index _dafny.Int) interface{} {
  {
    return ((_this.Data)).ArrayGet1((index).Int())
  }
}
func (_this *DynamicArray) Put(index _dafny.Int, element interface{}) {
  {
    var _arr0 _dafny.Array = _this.Data
    _ = _arr0
    (_arr0).ArraySet1(element, ((index)).Int())
  }
}
func (_this *DynamicArray) Ensure(reserved _dafny.Int, defaultValue interface{}) {
  {
    var _119_newCapacity _dafny.Int
    _ = _119_newCapacity
    _119_newCapacity = _this.Capacity
    for (reserved).Cmp((_119_newCapacity).Minus(_this.Size)) > 0 {
      _119_newCapacity = (_this).DefaultNewCapacity(_119_newCapacity)
    }
    if ((_119_newCapacity).Cmp(_this.Capacity) > 0) {
      (_this).Realloc(defaultValue, _119_newCapacity)
    }
  }
}
func (_this *DynamicArray) PopFast() {
  {
    (_this).Size = (_this.Size).Minus(_dafny.One)
  }
}
func (_this *DynamicArray) PushFast(element interface{}) {
  {
    var _arr1 _dafny.Array = _this.Data
    _ = _arr1
    var _index5 _dafny.Int = _this.Size
    _ = _index5
    (_arr1).ArraySet1(element, (_index5).Int())
    (_this).Size = (_this.Size).Plus(_dafny.One)
  }
}
func (_this *DynamicArray) Push(element interface{}) {
  {
    if ((_this.Size).Cmp(_this.Capacity) == 0) {
      (_this).ReallocDefault(element)
    }
    (_this).PushFast(element)
  }
}
func (_this *DynamicArray) Realloc(defaultValue interface{}, newCapacity _dafny.Int) {
  {
    var _120_oldData _dafny.Array
    _ = _120_oldData
    var _121_oldCapacity _dafny.Int
    _ = _121_oldCapacity
    var _rhs2 _dafny.Array = _this.Data
    _ = _rhs2
    var _rhs3 _dafny.Int = _this.Capacity
    _ = _rhs3
    _120_oldData = _rhs2
    _121_oldCapacity = _rhs3
    var _len0_3 _dafny.Int = newCapacity
    _ = _len0_3
    var _nw4 _dafny.Array
    _ = _nw4
    if (_len0_3.Cmp(_dafny.Zero) == 0) {
      _nw4 = _dafny.NewArray(_len0_3)
    } else {
      var _init3 func (_dafny.Int) interface{} = (func (_122_defaultValue interface{}) func (_dafny.Int) interface{} {
        return func (_123___v0 _dafny.Int) interface{} {
          return _122_defaultValue
        }
      })(defaultValue)
      _ = _init3
      var _element0_3 = _init3(_dafny.Zero)
      _ = _element0_3
      _nw4 = _dafny.NewArrayFromExample(_element0_3, nil, _len0_3)
      (_nw4).ArraySet1(_element0_3, 0)
      var _nativeLen0_3 = (_len0_3).Int()
      _ = _nativeLen0_3
      for _i0_3 := 1; _i0_3 < _nativeLen0_3; _i0_3++ {
        (_nw4).ArraySet1(_init3(_dafny.IntOf(_i0_3)), _i0_3)
      }
    }
    var _rhs4 _dafny.Array = _nw4
    _ = _rhs4
    var _rhs5 _dafny.Int = newCapacity
    _ = _rhs5
    var _lhs0 *DynamicArray = _this
    _ = _lhs0
    var _lhs1 *DynamicArray = _this
    _ = _lhs1
    _lhs0.Data = _rhs4
    _lhs1.Capacity = _rhs5
    (_this).CopyFrom(_120_oldData, _121_oldCapacity)
  }
}
func (_this *DynamicArray) DefaultNewCapacity(capacity _dafny.Int) _dafny.Int {
  {
    if ((capacity).Sign() == 0) {
      return _dafny.IntOfInt64(8)
    } else {
      return (_dafny.IntOfInt64(2)).Times(capacity)
    }
  }
}
func (_this *DynamicArray) ReallocDefault(defaultValue interface{}) {
  {
    (_this).Realloc(defaultValue, (_this).DefaultNewCapacity(_this.Capacity))
  }
}
func (_this *DynamicArray) CopyFrom(newData _dafny.Array, count _dafny.Int) {
  {
    for _iter8 := _dafny.Iterate(_dafny.IntegerRange(_dafny.Zero, count));; {
      _guard_loop_0, _ok8 := _iter8()
      if !_ok8 { break }
      var _124_index _dafny.Int
      _124_index = interface{}(_guard_loop_0).(_dafny.Int)
      if ((true) && (((_124_index).Sign() != -1) && ((_124_index).Cmp(count) < 0))) {
        var _arr2 _dafny.Array = _this.Data
        _ = _arr2
        (_arr2).ArraySet1(((newData)).ArrayGet1((_124_index).Int()), ((_124_index)).Int())
      }
    }
  }
}
// End of class DynamicArray
