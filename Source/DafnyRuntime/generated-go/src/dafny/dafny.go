// Package Dafny
// Dafny module Dafny compiled into Go

package Dafny

import (
  _dafny "dafny"
  _System "System_"
  Helpers_Compile "Helpers_Compile"
)
var _ _dafny.Dummy__
var _ _System.Dummy__

type Dummy__ struct{}


// Definition of trait Validatable
type Validatable interface {
}
type CompanionStruct_Validatable_ struct {
  TraitID_ *_dafny.TraitID
}
var Companion_Validatable_ = CompanionStruct_Validatable_ {
  TraitID_: &_dafny.TraitID{},
}
func (CompanionStruct_Validatable_) CastTo_(x interface{}) Validatable {
  var t Validatable
  t, _ = x.(Validatable)
  return t
}
// End of trait Validatable

// Definition of trait Array
type Array interface {
  Length() _dafny.Int
  Select(i _dafny.Int) interface{}
  Update(i _dafny.Int, t interface{})
  UpdateSubarray(start _dafny.Int, other Dafny.ImmutableArray)
  Freeze(size _dafny.Int) Dafny.ImmutableArray
}
type CompanionStruct_Array_ struct {
  TraitID_ *_dafny.TraitID
}
var Companion_Array_ = CompanionStruct_Array_ {
  TraitID_: &_dafny.TraitID{},
}
func (CompanionStruct_Array_) CastTo_(x interface{}) Array {
  var t Array
  t, _ = x.(Array)
  return t
}
// End of trait Array

// Definition of datatype ArrayCell
type ArrayCell struct {
  Data_ArrayCell_
}

func (_this ArrayCell) Get() Data_ArrayCell_ {
  return _this.Data_ArrayCell_
}

type Data_ArrayCell_ interface {
  isArrayCell()
}

type CompanionStruct_ArrayCell_ struct {
}
var Companion_ArrayCell_ = CompanionStruct_ArrayCell_ {
}

type ArrayCell_Set struct {
  Value interface{}
}

func (ArrayCell_Set) isArrayCell() {}

func (CompanionStruct_ArrayCell_) Create_Set_(Value interface{}) ArrayCell {
  return ArrayCell{ArrayCell_Set{Value}}
}

func (_this ArrayCell) Is_Set() bool {
  _, ok := _this.Get().(ArrayCell_Set)
  return ok
}

type ArrayCell_Unset struct {
}

func (ArrayCell_Unset) isArrayCell() {}

func (CompanionStruct_ArrayCell_) Create_Unset_() ArrayCell {
  return ArrayCell{ArrayCell_Unset{}}
}

func (_this ArrayCell) Is_Unset() bool {
  _, ok := _this.Get().(ArrayCell_Unset)
  return ok
}

func (CompanionStruct_ArrayCell_) Default() ArrayCell {
  return Companion_ArrayCell_.Create_Unset_()
}

func (_this ArrayCell) Dtor_value() interface{} {
  return _this.Get().(ArrayCell_Set).Value
}

func (_this ArrayCell) String() string {
  switch data := _this.Get().(type) {
    case nil: return "null"
    case ArrayCell_Set: {
      return "Dafny_Compile.ArrayCell.Set" + "(" + _dafny.String(data.Value) + ")"
    }
    case ArrayCell_Unset: {
      return "Dafny_Compile.ArrayCell.Unset"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this ArrayCell) Equals(other ArrayCell) bool {
  switch data1 := _this.Get().(type) {
    case ArrayCell_Set: {
      data2, ok := other.Get().(ArrayCell_Set)
      return ok && _dafny.AreEqual(data1.Value, data2.Value)
    }
    case ArrayCell_Unset: {
      _, ok := other.Get().(ArrayCell_Unset)
      return ok
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this ArrayCell) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(ArrayCell)
  return ok && _this.Equals(typed)
}

func Type_ArrayCell_() _dafny.TypeDescriptor {
  return type_ArrayCell_{}
}

type type_ArrayCell_ struct {
}

func (_this type_ArrayCell_) Default() interface{} {
  return Companion_ArrayCell_.Default();
}

func (_this type_ArrayCell_) String() string {
  return "Dafny.ArrayCell"
}
// End of datatype ArrayCell

// Definition of trait ImmutableArray
type ImmutableArray interface {
  Length() _dafny.Int
  Select(index _dafny.Int) interface{}
  Subarray(lo _dafny.Int, hi _dafny.Int) Dafny.ImmutableArray
}
type CompanionStruct_ImmutableArray_ struct {
  TraitID_ *_dafny.TraitID
}
var Companion_ImmutableArray_ = CompanionStruct_ImmutableArray_ {
  TraitID_: &_dafny.TraitID{},
}
func (CompanionStruct_ImmutableArray_) CastTo_(x interface{}) ImmutableArray {
  var t ImmutableArray
  t, _ = x.(ImmutableArray)
  return t
}
// End of trait ImmutableArray

// Definition of class Vector
type Vector struct {
  Storage Dafny.Array
  Size _dafny.Int
}

func New_Vector_() *Vector {
  _this := Vector{}

  _this.Storage = (Dafny.Array)(nil)
  _this.Size = _dafny.Zero
  return &_this
}

type CompanionStruct_Vector_ struct {
}
var Companion_Vector_ = CompanionStruct_Vector_ {
}

func (_this *Vector) Equals(other *Vector) bool {
  return _this == other
}

func (_this *Vector) EqualsGeneric(x interface{}) bool {
  other, ok := x.(*Vector)
  return ok && _this.Equals(other)
}

func (*Vector) String() string {
  return "Dafny.Vector"
}

func Type_Vector_(Type_T_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_Vector_{Type_T_}
}

type type_Vector_ struct {
  Type_T_ _dafny.TypeDescriptor
}

func (_this type_Vector_) Default() interface{} {
  return (*Vector)(nil)
}

func (_this type_Vector_) String() string {
  return "Dafny.Vector"
}
func (_this *Vector) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){Companion_Validatable_.TraitID_};
}
var _ Validatable = &Vector{}
var _ _dafny.TraitOffspring = &Vector{}
func (_this *Vector) Ctor__(length _dafny.Int) {
  {
    var _0_storage Dafny.Array
    _ = _0_storage
    var _out0 Dafny.Array
    _ = _out0
    _out0 = Dafny.NewArray(length)
    _0_storage = _out0
    (_this).Storage = _0_storage
    (_this).Size = _dafny.Zero
  }
}
func (_this *Vector) Select(index _dafny.Int) interface{} {
  {
    return (_this.Storage).Select(index)
  }
}
func (_this *Vector) Last() interface{} {
  {
    return (_this.Storage).Select((_this.Size).Minus((_dafny.One)))
  }
}
func (_this *Vector) AddLast(t interface{}) {
  {
    if ((_this.Size).Cmp(((_this.Storage).Length())) == 0) {
      (_this).Reallocate((_this).Max((_this).MIN__SIZE(), ((_this.Storage).Length()).Times((_dafny.IntOfInt64(2)))))
    }
    (_this.Storage).Update(_this.Size, t)
    (_this).Size = (_this.Size).Plus((_dafny.One))
  }
}
func (_this *Vector) Max(a _dafny.Int, b _dafny.Int) _dafny.Int {
  {
    if ((a).Cmp((b)) < 0) {
      return b
    } else {
      return a
    }
  }
}
func (_this *Vector) Reallocate(newCapacity _dafny.Int) {
  {
    var _1_newStorage Dafny.Array
    _ = _1_newStorage
    var _out1 Dafny.Array
    _ = _out1
    _out1 = Dafny.NewArray(newCapacity)
    _1_newStorage = _out1
    var _2_values Dafny.ImmutableArray
    _ = _2_values
    var _out2 Dafny.ImmutableArray
    _ = _out2
    _out2 = (_this.Storage).Freeze(_this.Size)
    _2_values = _out2
    (_1_newStorage).UpdateSubarray(_dafny.Zero, _2_values)
    (_this).Storage = _1_newStorage
  }
}
func (_this *Vector) RemoveLast() interface{} {
  {
    var t interface{} = (interface{})(nil)
    _ = t
    t = (_this.Storage).Select((_this.Size).Minus((_dafny.One)))
    (_this).Size = (_this.Size).Minus((_dafny.One))
    return t
  }
}
func (_this *Vector) Append(other Dafny.ImmutableArray) {
  {
    var _3_newSize _dafny.Int
    _ = _3_newSize
    _3_newSize = (_this.Size).Plus(((other).Length()))
    if (((_this.Storage).Length()).Cmp((_3_newSize)) < 0) {
      (_this).Reallocate((_this).Max(_3_newSize, ((_this.Storage).Length()).Times((_dafny.IntOfInt64(2)))))
    }
    (_this.Storage).UpdateSubarray(_this.Size, other)
    (_this).Size = (_this.Size).Plus(((other).Length()))
  }
}
func (_this *Vector) Freeze() Dafny.ImmutableArray {
  {
    var ret Dafny.ImmutableArray = (Dafny.ImmutableArray)(nil)
    _ = ret
    var _out3 Dafny.ImmutableArray
    _ = _out3
    _out3 = (_this.Storage).Freeze(_this.Size)
    ret = _out3
    return ret
  }
}
func (_this *Vector) MIN__SIZE() _dafny.Int {
  {
    return _dafny.IntOfInt64(10)
  }
}
// End of class Vector


// Definition of trait Sequence
type Sequence interface {
  Length() _dafny.Int
  HashCode() uint32
  ToString() _dafny.Seq
  Select(index _dafny.Int) interface{}
  Drop(lo _dafny.Int) Dafny.Sequence
  Take(hi _dafny.Int) Dafny.Sequence
  Subsequence(lo _dafny.Int, hi _dafny.Int) Dafny.Sequence
  ToArray() Dafny.ImmutableArray
}
func (_static *CompanionStruct_Sequence_) HashCode(_this Dafny.Sequence) uint32 {
  {
    var ret uint32 = 0
    _ = ret
    ret = uint32(0)
    var _hi0 = (_this).Length()
    for _4_i := _dafny.Zero; _4_i.Cmp(_hi0) < 0; _4_i = _4_i.Plus(_dafny.One) {
      var _5_element interface{}
      _ = _5_element
      var _out4 interface{}
      _ = _out4
      _out4 = (_this).Select(_4_i)
      _5_element = _out4
      ret = (((ret) << (_dafny.IntOfInt64(3)).Uint64()) | ((ret) >> (_dafny.IntOfInt64(29)).Uint64())) ^ (Helpers_Compile.HashCode(_5_element))
    }
    return ret
  }
}
func (_static *CompanionStruct_Sequence_) ToString(_this Dafny.Sequence) _dafny.Seq {
  {
    var ret _dafny.Seq = _dafny.EmptySeq.SetString()
    _ = ret
    ret = _dafny.SeqOfString("[")
    var _hi1 = (_this).Length()
    for _6_i := _dafny.Zero; _6_i.Cmp(_hi1) < 0; _6_i = _6_i.Plus(_dafny.One) {
      if ((_6_i).Sign() != 0) {
        ret = (ret).Concat((_dafny.SeqOfString(",")))
      }
      var _7_element interface{}
      _ = _7_element
      var _out5 interface{}
      _ = _out5
      _out5 = (_this).Select(_6_i)
      _7_element = _out5
      ret = (ret).Concat((Helpers_Compile.ToString(_7_element)))
    }
    ret = (ret).Concat((_dafny.SeqOfString("]")))
    return ret
  }
}
func (_static *CompanionStruct_Sequence_) Select(_this Dafny.Sequence, index _dafny.Int) interface{} {
  {
    var ret interface{} = (interface{})(nil)
    _ = ret
    var _8_a Dafny.ImmutableArray
    _ = _8_a
    var _out6 Dafny.ImmutableArray
    _ = _out6
    _out6 = (_this).ToArray()
    _8_a = _out6
    ret = (_8_a).Select(index)
    return ret
    return ret
  }
}
func (_static *CompanionStruct_Sequence_) Drop(_this Dafny.Sequence, lo _dafny.Int) Dafny.Sequence {
  {
    var ret Dafny.Sequence = (Dafny.Sequence)(nil)
    _ = ret
    var _out7 Dafny.Sequence
    _ = _out7
    _out7 = (_this).Subsequence(lo, (_this).Length())
    ret = _out7
    return ret
  }
}
func (_static *CompanionStruct_Sequence_) Take(_this Dafny.Sequence, hi _dafny.Int) Dafny.Sequence {
  {
    var ret Dafny.Sequence = (Dafny.Sequence)(nil)
    _ = ret
    var _out8 Dafny.Sequence
    _ = _out8
    _out8 = (_this).Subsequence(_dafny.Zero, hi)
    ret = _out8
    return ret
  }
}
func (_static *CompanionStruct_Sequence_) Subsequence(_this Dafny.Sequence, lo _dafny.Int, hi _dafny.Int) Dafny.Sequence {
  {
    var ret Dafny.Sequence = (Dafny.Sequence)(nil)
    _ = ret
    var _9_a Dafny.ImmutableArray
    _ = _9_a
    var _out9 Dafny.ImmutableArray
    _ = _out9
    _out9 = (_this).ToArray()
    _9_a = _out9
    var _10_subarray Dafny.ImmutableArray
    _ = _10_subarray
    var _out10 Dafny.ImmutableArray
    _ = _out10
    _out10 = (_9_a).Subarray(lo, hi)
    _10_subarray = _out10
    var _nw0 *ArraySequence = New_ArraySequence_()
    _ = _nw0
    _nw0.Ctor__(_10_subarray)
    ret = _nw0
    return ret
  }
}
type CompanionStruct_Sequence_ struct {
  TraitID_ *_dafny.TraitID
}
var Companion_Sequence_ = CompanionStruct_Sequence_ {
  TraitID_: &_dafny.TraitID{},
}
func (CompanionStruct_Sequence_) CastTo_(x interface{}) Sequence {
  var t Sequence
  t, _ = x.(Sequence)
  return t
}
// End of trait Sequence

// Definition of class ArraySequence
type ArraySequence struct {
  _value Dafny.ImmutableArray
}

func New_ArraySequence_() *ArraySequence {
  _this := ArraySequence{}

  _this._value = (Dafny.ImmutableArray)(nil)
  return &_this
}

type CompanionStruct_ArraySequence_ struct {
}
var Companion_ArraySequence_ = CompanionStruct_ArraySequence_ {
}

func (_this *ArraySequence) Equals(other *ArraySequence) bool {
  return _this == other
}

func (_this *ArraySequence) EqualsGeneric(x interface{}) bool {
  other, ok := x.(*ArraySequence)
  return ok && _this.Equals(other)
}

func (*ArraySequence) String() string {
  return "Dafny.ArraySequence"
}

func Type_ArraySequence_(Type_T_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_ArraySequence_{Type_T_}
}

type type_ArraySequence_ struct {
  Type_T_ _dafny.TypeDescriptor
}

func (_this type_ArraySequence_) Default() interface{} {
  return (*ArraySequence)(nil)
}

func (_this type_ArraySequence_) String() string {
  return "Dafny.ArraySequence"
}
func (_this *ArraySequence) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){Companion_Sequence_.TraitID_};
}
var _ Dafny.Sequence = &ArraySequence{}
var _ _dafny.TraitOffspring = &ArraySequence{}
func (_this *ArraySequence) HashCode() uint32 {
  var _out11 uint32
  _ = _out11
  _out11 = Dafny.Companion_Sequence_.HashCode(_this)
  return _out11
}
func (_this *ArraySequence) ToString() _dafny.Seq {
  var _out12 _dafny.Seq
  _ = _out12
  _out12 = Dafny.Companion_Sequence_.ToString(_this)
  return _out12
}
func (_this *ArraySequence) Select(index _dafny.Int) interface{} {
  var _out13 interface{}
  _ = _out13
  _out13 = Dafny.Companion_Sequence_.Select(_this, index)
  return _out13
}
func (_this *ArraySequence) Drop(lo _dafny.Int) Dafny.Sequence {
  var _out14 Dafny.Sequence
  _ = _out14
  _out14 = Dafny.Companion_Sequence_.Drop(_this, lo)
  return _out14
}
func (_this *ArraySequence) Take(hi _dafny.Int) Dafny.Sequence {
  var _out15 Dafny.Sequence
  _ = _out15
  _out15 = Dafny.Companion_Sequence_.Take(_this, hi)
  return _out15
}
func (_this *ArraySequence) Subsequence(lo _dafny.Int, hi _dafny.Int) Dafny.Sequence {
  var _out16 Dafny.Sequence
  _ = _out16
  _out16 = Dafny.Companion_Sequence_.Subsequence(_this, lo, hi)
  return _out16
}
func (_this *ArraySequence) Ctor__(value Dafny.ImmutableArray) {
  {
    (_this)._value = value
  }
}
func (_this *ArraySequence) Length() _dafny.Int {
  {
    return ((_this).Go__value()).Length()
  }
}
func (_this *ArraySequence) ToArray() Dafny.ImmutableArray {
  {
    var ret Dafny.ImmutableArray = (Dafny.ImmutableArray)(nil)
    _ = ret
    ret = (_this).Go__value()
    return ret
    return ret
  }
}
func (_this *ArraySequence) Go__value() Dafny.ImmutableArray {
  {
    return _this._value
  }
}
// End of class ArraySequence

// Definition of class ConcatSequence
type ConcatSequence struct {
  _left Dafny.Sequence
  _right Dafny.Sequence
  _length _dafny.Int
}

func New_ConcatSequence_() *ConcatSequence {
  _this := ConcatSequence{}

  _this._left = (Dafny.Sequence)(nil)
  _this._right = (Dafny.Sequence)(nil)
  _this._length = _dafny.Zero
  return &_this
}

type CompanionStruct_ConcatSequence_ struct {
}
var Companion_ConcatSequence_ = CompanionStruct_ConcatSequence_ {
}

func (_this *ConcatSequence) Equals(other *ConcatSequence) bool {
  return _this == other
}

func (_this *ConcatSequence) EqualsGeneric(x interface{}) bool {
  other, ok := x.(*ConcatSequence)
  return ok && _this.Equals(other)
}

func (*ConcatSequence) String() string {
  return "Dafny.ConcatSequence"
}

func Type_ConcatSequence_(Type_T_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_ConcatSequence_{Type_T_}
}

type type_ConcatSequence_ struct {
  Type_T_ _dafny.TypeDescriptor
}

func (_this type_ConcatSequence_) Default() interface{} {
  return (*ConcatSequence)(nil)
}

func (_this type_ConcatSequence_) String() string {
  return "Dafny.ConcatSequence"
}
func (_this *ConcatSequence) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){Companion_Sequence_.TraitID_};
}
var _ Dafny.Sequence = &ConcatSequence{}
var _ _dafny.TraitOffspring = &ConcatSequence{}
func (_this *ConcatSequence) HashCode() uint32 {
  var _out17 uint32
  _ = _out17
  _out17 = Dafny.Companion_Sequence_.HashCode(_this)
  return _out17
}
func (_this *ConcatSequence) ToString() _dafny.Seq {
  var _out18 _dafny.Seq
  _ = _out18
  _out18 = Dafny.Companion_Sequence_.ToString(_this)
  return _out18
}
func (_this *ConcatSequence) Select(index _dafny.Int) interface{} {
  var _out19 interface{}
  _ = _out19
  _out19 = Dafny.Companion_Sequence_.Select(_this, index)
  return _out19
}
func (_this *ConcatSequence) Drop(lo _dafny.Int) Dafny.Sequence {
  var _out20 Dafny.Sequence
  _ = _out20
  _out20 = Dafny.Companion_Sequence_.Drop(_this, lo)
  return _out20
}
func (_this *ConcatSequence) Take(hi _dafny.Int) Dafny.Sequence {
  var _out21 Dafny.Sequence
  _ = _out21
  _out21 = Dafny.Companion_Sequence_.Take(_this, hi)
  return _out21
}
func (_this *ConcatSequence) Subsequence(lo _dafny.Int, hi _dafny.Int) Dafny.Sequence {
  var _out22 Dafny.Sequence
  _ = _out22
  _out22 = Dafny.Companion_Sequence_.Subsequence(_this, lo, hi)
  return _out22
}
func (_this *ConcatSequence) Ctor__(left Dafny.Sequence, right Dafny.Sequence) {
  {
    (_this)._left = left
    (_this)._right = right
    (_this)._length = ((left).Length()).Plus(((right).Length()))
  }
}
func (_this *ConcatSequence) Length() _dafny.Int {
  {
    return (_this).Go__length()
  }
}
func (_this *ConcatSequence) ToArray() Dafny.ImmutableArray {
  {
    var ret Dafny.ImmutableArray = (Dafny.ImmutableArray)(nil)
    _ = ret
    var _11_builder *Vector
    _ = _11_builder
    var _nw1 *Vector = New_Vector_()
    _ = _nw1
    _nw1.Ctor__((_this).Go__length())
    _11_builder = _nw1
    var _12_stack *Vector
    _ = _12_stack
    var _nw2 *Vector = New_Vector_()
    _ = _nw2
    _nw2.Ctor__(_dafny.IntOfInt64(10))
    _12_stack = _nw2
    Companion_Default___.AppendOptimized(_11_builder, _this, _12_stack)
    var _out23 Dafny.ImmutableArray
    _ = _out23
    _out23 = (_11_builder).Freeze()
    ret = _out23
    return ret
  }
}
func (_this *ConcatSequence) Left() Dafny.Sequence {
  {
    return _this._left
  }
}
func (_this *ConcatSequence) Right() Dafny.Sequence {
  {
    return _this._right
  }
}
func (_this *ConcatSequence) Go__length() _dafny.Int {
  {
    return _this._length
  }
}
// End of class ConcatSequence

// Definition of class LazySequence
type LazySequence struct {
  _length _dafny.Int
  _box *Dafny.AtomicBox
}

func New_LazySequence_() *LazySequence {
  _this := LazySequence{}

  _this._length = _dafny.Zero
  _this._box = (*Dafny.AtomicBox)(nil)
  return &_this
}

type CompanionStruct_LazySequence_ struct {
}
var Companion_LazySequence_ = CompanionStruct_LazySequence_ {
}

func (_this *LazySequence) Equals(other *LazySequence) bool {
  return _this == other
}

func (_this *LazySequence) EqualsGeneric(x interface{}) bool {
  other, ok := x.(*LazySequence)
  return ok && _this.Equals(other)
}

func (*LazySequence) String() string {
  return "Dafny.LazySequence"
}

func Type_LazySequence_(Type_T_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_LazySequence_{Type_T_}
}

type type_LazySequence_ struct {
  Type_T_ _dafny.TypeDescriptor
}

func (_this type_LazySequence_) Default() interface{} {
  return (*LazySequence)(nil)
}

func (_this type_LazySequence_) String() string {
  return "Dafny.LazySequence"
}
func (_this *LazySequence) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){Companion_Sequence_.TraitID_};
}
var _ Dafny.Sequence = &LazySequence{}
var _ _dafny.TraitOffspring = &LazySequence{}
func (_this *LazySequence) HashCode() uint32 {
  var _out24 uint32
  _ = _out24
  _out24 = Dafny.Companion_Sequence_.HashCode(_this)
  return _out24
}
func (_this *LazySequence) ToString() _dafny.Seq {
  var _out25 _dafny.Seq
  _ = _out25
  _out25 = Dafny.Companion_Sequence_.ToString(_this)
  return _out25
}
func (_this *LazySequence) Select(index _dafny.Int) interface{} {
  var _out26 interface{}
  _ = _out26
  _out26 = Dafny.Companion_Sequence_.Select(_this, index)
  return _out26
}
func (_this *LazySequence) Drop(lo _dafny.Int) Dafny.Sequence {
  var _out27 Dafny.Sequence
  _ = _out27
  _out27 = Dafny.Companion_Sequence_.Drop(_this, lo)
  return _out27
}
func (_this *LazySequence) Take(hi _dafny.Int) Dafny.Sequence {
  var _out28 Dafny.Sequence
  _ = _out28
  _out28 = Dafny.Companion_Sequence_.Take(_this, hi)
  return _out28
}
func (_this *LazySequence) Subsequence(lo _dafny.Int, hi _dafny.Int) Dafny.Sequence {
  var _out29 Dafny.Sequence
  _ = _out29
  _out29 = Dafny.Companion_Sequence_.Subsequence(_this, lo, hi)
  return _out29
}
func (_this *LazySequence) Ctor__(wrapped Dafny.Sequence) {
  {
    var _13_box *Dafny.AtomicBox
    _ = _13_box
    var _out30 *Dafny.AtomicBox
    _ = _out30
    _out30 = Dafny.Companion_AtomicBox_.Make(wrapped)
    _13_box = _out30
    (_this)._box = _13_box
    (_this)._length = (wrapped).Length()
  }
}
func (_this *LazySequence) Length() _dafny.Int {
  {
    return (_this).Go__length()
  }
}
func (_this *LazySequence) ToArray() Dafny.ImmutableArray {
  {
    var ret Dafny.ImmutableArray = (Dafny.ImmutableArray)(nil)
    _ = ret
    var _14_expr Dafny.Sequence
    _ = _14_expr
    var _out31 interface{}
    _ = _out31
    _out31 = ((_this).Box()).Get()
    _14_expr = Dafny.Companion_Sequence_.CastTo_(_out31)
    var _out32 Dafny.ImmutableArray
    _ = _out32
    _out32 = (_14_expr).ToArray()
    ret = _out32
    var _15_arraySeq *ArraySequence
    _ = _15_arraySeq
    var _nw3 *ArraySequence = New_ArraySequence_()
    _ = _nw3
    _nw3.Ctor__(ret)
    _15_arraySeq = _nw3
    ((_this).Box()).Put(_15_arraySeq)
    return ret
  }
}
func (_this *LazySequence) Go__length() _dafny.Int {
  {
    return _this._length
  }
}
func (_this *LazySequence) Box() *Dafny.AtomicBox {
  {
    return _this._box
  }
}
// End of class LazySequence

// Definition of class Default__
type Default__ struct {
  dummy byte
}

func New_Default___() *Default__ {
  _this := Default__{}

  return &_this
}

type CompanionStruct_Default___ struct {
}
var Companion_Default___ = CompanionStruct_Default___ {
}

func (_this *Default__) Equals(other *Default__) bool {
  return _this == other
}

func (_this *Default__) EqualsGeneric(x interface{}) bool {
  other, ok := x.(*Default__)
  return ok && _this.Equals(other)
}

func (*Default__) String() string {
  return "Dafny.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}
func (_static *CompanionStruct_Default___) AppendRecursive(builder *Vector, e Dafny.Sequence) {
  if (func (_is_0 Dafny.Sequence) bool {
    return _dafny.InstanceOf(_is_0, (*ConcatSequence)(nil))
  }(e)) {
    var _16_concat *ConcatSequence
    _ = _16_concat
    _16_concat = e.(*ConcatSequence)
    Companion_Default___.AppendRecursive(builder, (_16_concat).Left())
    Companion_Default___.AppendRecursive(builder, (_16_concat).Right())
  } else if (func (_is_1 Dafny.Sequence) bool {
    return _dafny.InstanceOf(_is_1, (*LazySequence)(nil))
  }(e)) {
    var _17_lazy *LazySequence
    _ = _17_lazy
    _17_lazy = e.(*LazySequence)
    var _18_boxed Dafny.Sequence
    _ = _18_boxed
    var _out33 interface{}
    _ = _out33
    _out33 = ((_17_lazy).Box()).Get()
    _18_boxed = Dafny.Companion_Sequence_.CastTo_(_out33)
    Companion_Default___.AppendRecursive(builder, _18_boxed)
  } else {
    var _19_a Dafny.ImmutableArray
    _ = _19_a
    var _out34 Dafny.ImmutableArray
    _ = _out34
    _out34 = (e).ToArray()
    _19_a = _out34
    (builder).Append(_19_a)
  }
}
func (_static *CompanionStruct_Default___) AppendOptimized(builder *Vector, e Dafny.Sequence, stack *Vector) {
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if (func (_is_2 Dafny.Sequence) bool {
    return _dafny.InstanceOf(_is_2, (*ConcatSequence)(nil))
  }(e)) {
    var _20_concat *ConcatSequence
    _ = _20_concat
    _20_concat = e.(*ConcatSequence)
    (stack).AddLast((_20_concat).Right())
    var _in0 *Vector = builder
    _ = _in0
    var _in1 Dafny.Sequence = (_20_concat).Left()
    _ = _in1
    var _in2 *Vector = stack
    _ = _in2
    builder = _in0
    e = _in1
    stack = _in2
    goto TAIL_CALL_START
  } else if (func (_is_3 Dafny.Sequence) bool {
    return _dafny.InstanceOf(_is_3, (*LazySequence)(nil))
  }(e)) {
    var _21_lazy *LazySequence
    _ = _21_lazy
    _21_lazy = e.(*LazySequence)
    var _22_boxed Dafny.Sequence
    _ = _22_boxed
    var _out35 interface{}
    _ = _out35
    _out35 = ((_21_lazy).Box()).Get()
    _22_boxed = Dafny.Companion_Sequence_.CastTo_(_out35)
    var _in3 *Vector = builder
    _ = _in3
    var _in4 Dafny.Sequence = _22_boxed
    _ = _in4
    var _in5 *Vector = stack
    _ = _in5
    builder = _in3
    e = _in4
    stack = _in5
    goto TAIL_CALL_START
  } else if (func (_is_4 Dafny.Sequence) bool {
    return _dafny.InstanceOf(_is_4, (*ArraySequence)(nil))
  }(e)) {
    var _23_a *ArraySequence
    _ = _23_a
    _23_a = e.(*ArraySequence)
    (builder).Append((_23_a).Go__value())
    if ((stack.Size).Sign() == 1) {
      var _24_next Dafny.Sequence
      _ = _24_next
      var _out36 interface{}
      _ = _out36
      _out36 = (stack).RemoveLast()
      _24_next = Dafny.Companion_Sequence_.CastTo_(_out36)
      var _in6 *Vector = builder
      _ = _in6
      var _in7 Dafny.Sequence = _24_next
      _ = _in7
      var _in8 *Vector = stack
      _ = _in8
      builder = _in6
      e = _in7
      stack = _in8
      goto TAIL_CALL_START
    }
  } else {
  }
}
func (_static *CompanionStruct_Default___) EqualUpTo(left Dafny.Sequence, right Dafny.Sequence, index _dafny.Int) bool {
  var ret bool = false
  _ = ret
  var _hi2 = index
  for _25_i := _dafny.Zero; _25_i.Cmp(_hi2) < 0; _25_i = _25_i.Plus(_dafny.One) {
    var _26_leftElement interface{}
    _ = _26_leftElement
    var _out37 interface{}
    _ = _out37
    _out37 = (left).Select(_25_i)
    _26_leftElement = _out37
    var _27_rightElement interface{}
    _ = _27_rightElement
    var _out38 interface{}
    _ = _out38
    _out38 = (right).Select(_25_i)
    _27_rightElement = _out38
    if (!_dafny.AreEqual(_26_leftElement, _27_rightElement)) {
      ret = false
      return ret
    }
  }
  ret = true
  return ret
  return ret
}
func (_static *CompanionStruct_Default___) EqualSequences(left Dafny.Sequence, right Dafny.Sequence) bool {
  var ret bool = false
  _ = ret
  if (((left).Length()).Cmp(((right).Length())) != 0) {
    ret = false
    return ret
  }
  var _out39 bool
  _ = _out39
  _out39 = Companion_Default___.EqualUpTo(left, right, (left).Length())
  ret = _out39
  return ret
}
func (_static *CompanionStruct_Default___) IsPrefixOf(left Dafny.Sequence, right Dafny.Sequence) bool {
  var ret bool = false
  _ = ret
  if (((right).Length()).Cmp(((left).Length())) < 0) {
    ret = false
    return ret
  }
  var _out40 bool
  _ = _out40
  _out40 = Companion_Default___.EqualUpTo(left, right, (left).Length())
  ret = _out40
  return ret
}
func (_static *CompanionStruct_Default___) IsProperPrefixOf(left Dafny.Sequence, right Dafny.Sequence) bool {
  var ret bool = false
  _ = ret
  if (((right).Length()).Cmp(((left).Length())) <= 0) {
    ret = false
    return ret
  }
  var _out41 bool
  _ = _out41
  _out41 = Companion_Default___.EqualUpTo(left, right, (left).Length())
  ret = _out41
  return ret
}
func (_static *CompanionStruct_Default___) Contains(s Dafny.Sequence, t interface{}) bool {
  var _hresult bool = false
  _ = _hresult
  var _hi3 = (s).Length()
  for _28_i := _dafny.Zero; _28_i.Cmp(_hi3) < 0; _28_i = _28_i.Plus(_dafny.One) {
    var _29_element interface{}
    _ = _29_element
    var _out42 interface{}
    _ = _out42
    _out42 = (s).Select(_28_i)
    _29_element = _out42
    if (_dafny.AreEqual(_29_element, t)) {
      _hresult = true
      return _hresult
    }
  }
  _hresult = false
  return _hresult
  return _hresult
}
func (_static *CompanionStruct_Default___) Concatenate(left Dafny.Sequence, right Dafny.Sequence) Dafny.Sequence {
  var ret Dafny.Sequence = (Dafny.Sequence)(nil)
  _ = ret
  var _30_c *ConcatSequence
  _ = _30_c
  var _nw4 *ConcatSequence = New_ConcatSequence_()
  _ = _nw4
  _nw4.Ctor__(left, right)
  _30_c = _nw4
  var _nw5 *LazySequence = New_LazySequence_()
  _ = _nw5
  _nw5.Ctor__(_30_c)
  ret = _nw5
  return ret
}
func (_static *CompanionStruct_Default___) Update(s Dafny.Sequence, i _dafny.Int, t interface{}) Dafny.Sequence {
  var ret Dafny.Sequence = (Dafny.Sequence)(nil)
  _ = ret
  var _31_a Dafny.ImmutableArray
  _ = _31_a
  var _out43 Dafny.ImmutableArray
  _ = _out43
  _out43 = (s).ToArray()
  _31_a = _out43
  var _32_newValue Dafny.Array
  _ = _32_newValue
  var _out44 Dafny.Array
  _ = _out44
  _out44 = Dafny.CopyArray(_31_a)
  _32_newValue = _out44
  (_32_newValue).Update(i, t)
  var _33_newValueFrozen Dafny.ImmutableArray
  _ = _33_newValueFrozen
  var _out45 Dafny.ImmutableArray
  _ = _out45
  _out45 = (_32_newValue).Freeze((_32_newValue).Length())
  _33_newValueFrozen = _out45
  var _nw6 *ArraySequence = New_ArraySequence_()
  _ = _nw6
  _nw6.Ctor__(_33_newValueFrozen)
  ret = _nw6
  return ret
}
func (_static *CompanionStruct_Default___) MultiDimentionalArrays() {
  var _34_a *_dafny.Array
  _ = _34_a
  var _nw7 *_dafny.Array = _dafny.NewArray(_dafny.IntOfInt64(3), _dafny.IntOfInt64(4), _dafny.IntOfInt64(5))
  _ = _nw7
  var _arrayinit0 func (_dafny.Int, _dafny.Int, _dafny.Int) _dafny.Int = func (_35_i _dafny.Int, _36_j _dafny.Int, _37_k _dafny.Int) _dafny.Int {
    return _dafny.Zero
  }
  _ = _arrayinit0
  for _arrayinit_00 := _dafny.Zero; _arrayinit_00.Cmp(_nw7.Len(0)) < 0; _arrayinit_00 = _arrayinit_00.Plus(_dafny.One) {
    for _arrayinit_10 := _dafny.Zero; _arrayinit_10.Cmp(_nw7.Len(1)) < 0; _arrayinit_10 = _arrayinit_10.Plus(_dafny.One) {
      for _arrayinit_20 := _dafny.Zero; _arrayinit_20.Cmp(_nw7.Len(2)) < 0; _arrayinit_20 = _arrayinit_20.Plus(_dafny.One) {
        *(_nw7.Index(_dafny.IntOfAny(_arrayinit_00), _dafny.IntOfAny(_arrayinit_10), _dafny.IntOfAny(_arrayinit_20))) = _arrayinit0(_arrayinit_00, _arrayinit_10, _arrayinit_20)
      }
    }
  }
  _34_a = _nw7
  *((_34_a).Index(_dafny.IntOfAny((_dafny.One)), _dafny.IntOfAny((_dafny.One)), _dafny.IntOfAny((_dafny.One)))) = _dafny.IntOfInt64(42)
}
// End of class Default__
