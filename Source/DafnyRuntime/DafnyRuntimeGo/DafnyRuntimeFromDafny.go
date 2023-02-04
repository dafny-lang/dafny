// Package dafny
// Dafny module dafny compiled into Go

package dafny

import (
)

type Dummy__ struct{}


// Definition of trait Sequence
type Sequence interface {
  String() string
  Equals(other Sequence) bool
  EqualsGeneric(x interface{}) bool
  VerbatimString(isLiteral bool) string
  SetString() Sequence
  IsString() bool
  IsString_set_(value bool)
  Cardinality() uint32
  Select(index uint32) interface{}
  Drop(lo uint32) Sequence
  Take(hi uint32) Sequence
  Subsequence(lo uint32, hi uint32) Sequence
  ToArray() ImmutableArray
  Elements() Sequence
  UniqueElements() Set
}
func (_static *CompanionStruct_Sequence_) SetString(_this Sequence) Sequence {
  {
    var ret Sequence = (Sequence)(nil)
    _ = ret
    (_this).IsString_set_(true);
    ret = _this
    return ret
    return ret
  }
}
func (_static *CompanionStruct_Sequence_) Select(_this Sequence, index uint32) interface{} {
  {
    var ret interface{} = (interface{})(nil)
    _ = ret
    var _0_a ImmutableArray
    _ = _0_a
    var _out0 ImmutableArray
    _ = _out0
    _out0 = (_this).ToArray()
    _0_a = _out0
    ret = (_0_a).Select(index)
    return ret
    return ret
  }
}
func (_static *CompanionStruct_Sequence_) Drop(_this Sequence, lo uint32) Sequence {
  {
    var ret Sequence = (Sequence)(nil)
    _ = ret
    var _out1 Sequence
    _ = _out1
    _out1 = (_this).Subsequence(lo, (_this).Cardinality())
    ret = _out1
    return ret
  }
}
func (_static *CompanionStruct_Sequence_) Take(_this Sequence, hi uint32) Sequence {
  {
    var ret Sequence = (Sequence)(nil)
    _ = ret
    var _out2 Sequence
    _ = _out2
    _out2 = (_this).Subsequence(uint32(0), hi)
    ret = _out2
    return ret
  }
}
func (_static *CompanionStruct_Sequence_) Subsequence(_this Sequence, lo uint32, hi uint32) Sequence {
  {
    var ret Sequence = (Sequence)(nil)
    _ = ret
    var _1_a ImmutableArray
    _ = _1_a
    var _out3 ImmutableArray
    _ = _out3
    _out3 = (_this).ToArray()
    _1_a = _out3
    var _2_subarray ImmutableArray
    _ = _2_subarray
    var _out4 ImmutableArray
    _ = _out4
    _out4 = (_1_a).Subarray(lo, hi)
    _2_subarray = _out4
    var _nw0 *ArraySequence = New_ArraySequence_()
    _ = _nw0
    _nw0.Ctor__(_2_subarray, false)
    ret = _nw0
    return ret
  }
}
func (_static *CompanionStruct_Sequence_) Elements(_this Sequence) Sequence {
  {
    return _this
  }
}
func (_static *CompanionStruct_Sequence_) Create(cardinality uint32, initFn func (uint32) interface{}) Sequence {
  var ret Sequence = (Sequence)(nil)
  _ = ret
  var _3_a NativeArray
  _ = _3_a
  var _out5 NativeArray
  _ = _out5
  _out5 = Companion_NativeArray_.MakeWithInit(cardinality, func (coer0 func (uint32) interface{}) func (uint32) interface{} {
    return func (arg0 uint32) interface{} {
      return coer0(arg0)
    }
  }(initFn))
  _3_a = _out5
  var _4_frozen ImmutableArray
  _ = _4_frozen
  var _out6 ImmutableArray
  _ = _out6
  _out6 = (_3_a).Freeze(cardinality)
  _4_frozen = _out6
  var _nw1 *ArraySequence = New_ArraySequence_()
  _ = _nw1
  _nw1.Ctor__(_4_frozen, false)
  ret = _nw1
  return ret
}
func (_static *CompanionStruct_Sequence_) EqualUpTo(left Sequence, right Sequence, index uint32) bool {
  var ret bool = false
  _ = ret
  var _hi0 = index
  for _5_i := uint32(0); _5_i < _hi0; _5_i++ {
    var _6_leftElement interface{}
    _ = _6_leftElement
    var _out7 interface{}
    _ = _out7
    _out7 = (left).Select(_5_i)
    _6_leftElement = _out7
    var _7_rightElement interface{}
    _ = _7_rightElement
    var _out8 interface{}
    _ = _out8
    _out8 = (right).Select(_5_i)
    _7_rightElement = _out8
    if (!AreEqual(_6_leftElement, _7_rightElement)) {
      ret = false
      return ret
    }
  }
  ret = true
  return ret
  return ret
}
func (_static *CompanionStruct_Sequence_) Equal(left Sequence, right Sequence) bool {
  var ret bool = false
  _ = ret
  if (((left).Cardinality()) != ((right).Cardinality())/* dircomp */) {
    ret = false
    return ret
  }
  var _out9 bool
  _ = _out9
  _out9 = Companion_Sequence_.EqualUpTo(left, right, (left).Cardinality())
  ret = _out9
  return ret
}
func (_static *CompanionStruct_Sequence_) IsPrefixOf(left Sequence, right Sequence) bool {
  var ret bool = false
  _ = ret
  if (((right).Cardinality()) < ((left).Cardinality())) {
    ret = false
    return ret
  }
  var _out10 bool
  _ = _out10
  _out10 = Companion_Sequence_.EqualUpTo(left, right, (left).Cardinality())
  ret = _out10
  return ret
}
func (_static *CompanionStruct_Sequence_) IsProperPrefixOf(left Sequence, right Sequence) bool {
  var ret bool = false
  _ = ret
  if (((right).Cardinality()) <= ((left).Cardinality())) {
    ret = false
    return ret
  }
  var _out11 bool
  _ = _out11
  _out11 = Companion_Sequence_.EqualUpTo(left, right, (left).Cardinality())
  ret = _out11
  return ret
}
func (_static *CompanionStruct_Sequence_) Contains(s Sequence, t interface{}) bool {
  var _hresult bool = false
  _ = _hresult
  var _hi1 = (s).Cardinality()
  for _8_i := Companion_Default___.ZERO__SIZE(); _8_i < _hi1; _8_i++ {
    var _9_element interface{}
    _ = _9_element
    var _out12 interface{}
    _ = _out12
    _out12 = (s).Select(_8_i)
    _9_element = _out12
    if (AreEqual(_9_element, t)) {
      _hresult = true
      return _hresult
    }
  }
  _hresult = false
  return _hresult
  return _hresult
}
func (_static *CompanionStruct_Sequence_) Update(s Sequence, i uint32, t interface{}) Sequence {
  var ret Sequence = (Sequence)(nil)
  _ = ret
  var _10_a ImmutableArray
  _ = _10_a
  var _out13 ImmutableArray
  _ = _out13
  _out13 = (s).ToArray()
  _10_a = _out13
  var _11_newValue NativeArray
  _ = _11_newValue
  var _out14 NativeArray
  _ = _out14
  _out14 = Companion_NativeArray_.Copy(_10_a)
  _11_newValue = _out14
  (_11_newValue).Update(i, t)
  var _12_newValueFrozen ImmutableArray
  _ = _12_newValueFrozen
  var _out15 ImmutableArray
  _ = _out15
  _out15 = (_11_newValue).Freeze((_11_newValue).Length())
  _12_newValueFrozen = _out15
  var _nw2 *ArraySequence = New_ArraySequence_()
  _ = _nw2
  _nw2.Ctor__(_12_newValueFrozen, false)
  ret = _nw2
  return ret
}
func (_static *CompanionStruct_Sequence_) Concatenate(left Sequence, right Sequence) Sequence {
  var ret Sequence = (Sequence)(nil)
  _ = ret
  if (!(Companion_Default___.SizeAdditionInRange((left).Cardinality(), (right).Cardinality()))) {
    panic("/Users/salkeldr/Documents/GitHub/dafny/Source/DafnyRuntime/DafnyRuntimeDafny/src/dafnyRuntime.dfy[DafnyGo](580,6): " + (Companion_Sequence_.Concatenate(Companion_Sequence_.Concatenate(SeqOfString("Concatenation result cardinality would be larger than the maximum ("), Companion_Helpers_.DafnyValueToDafnyString(Companion_Default___.SIZE__T__MAX())), SeqOfString(")"))).String())
  }
  var _13_c *ConcatSequence
  _ = _13_c
  var _nw3 *ConcatSequence = New_ConcatSequence_()
  _ = _nw3
  _nw3.Ctor__(left, right)
  _13_c = _nw3
  var _nw4 *LazySequence = New_LazySequence_()
  _ = _nw4
  _nw4.Ctor__(_13_c)
  ret = _nw4
  return ret
}
type CompanionStruct_Sequence_ struct {
  TraitID_ *TraitID
}
var Companion_Sequence_ = CompanionStruct_Sequence_ {
  TraitID_: &TraitID{},
}
func (CompanionStruct_Sequence_) CastTo_(x interface{}) Sequence {
  var t Sequence
  t, _ = x.(Sequence)
  return t
}
// End of trait Sequence

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
  return "dafny.Default__"
}
func (_this *Default__) ParentTraits_() []*TraitID {
  return [](*TraitID){};
}
var _ TraitOffspring = &Default__{}
func (_static *CompanionStruct_Default___) SizeAdditionInRange(a uint32, b uint32) bool {
  var _hresult bool = false
  _ = _hresult
  _hresult = (a) <= ((Companion_Default___.SIZE__T__MAX()) - (func () uint32 { return  (b) })())
  return _hresult
  return _hresult
}
func (_static *CompanionStruct_Default___) AppendRecursive(builder *Vector, e Sequence) {
  if (func (_is_0 Sequence) bool {
    return InstanceOf(_is_0, (*ConcatSequence)(nil))
  }(e)) {
    var _14_concat *ConcatSequence
    _ = _14_concat
    _14_concat = e.(*ConcatSequence)
    Companion_Default___.AppendRecursive(builder, (_14_concat).Left())
    Companion_Default___.AppendRecursive(builder, (_14_concat).Right())
  } else if (func (_is_1 Sequence) bool {
    return InstanceOf(_is_1, (*LazySequence)(nil))
  }(e)) {
    var _15_lazy *LazySequence
    _ = _15_lazy
    _15_lazy = e.(*LazySequence)
    var _16_boxed Sequence
    _ = _16_boxed
    var _out16 interface{}
    _ = _out16
    _out16 = ((_15_lazy).Box()).Get()
    _16_boxed = Companion_Sequence_.CastTo_(_out16)
    Companion_Default___.AppendRecursive(builder, _16_boxed)
  } else {
    var _17_a ImmutableArray
    _ = _17_a
    var _out17 ImmutableArray
    _ = _out17
    _out17 = (e).ToArray()
    _17_a = _out17
    (builder).Append(_17_a)
  }
}
func (_static *CompanionStruct_Default___) AppendOptimized(builder *Vector, e Sequence, stack *Vector) {
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if (func (_is_2 Sequence) bool {
    return InstanceOf(_is_2, (*ConcatSequence)(nil))
  }(e)) {
    var _18_concat *ConcatSequence
    _ = _18_concat
    _18_concat = e.(*ConcatSequence)
    if (!(Companion_Default___.SizeAdditionInRange(stack.Size, Companion_Default___.ONE__SIZE()))) {
      panic("/Users/salkeldr/Documents/GitHub/dafny/Source/DafnyRuntime/DafnyRuntimeDafny/src/dafnyRuntime.dfy[DafnyGo](749,6): " + (SeqOfString("expectation violation")).String())
    }
    (stack).AddLast((_18_concat).Right())
    var _in0 *Vector = builder
    _ = _in0
    var _in1 Sequence = (_18_concat).Left()
    _ = _in1
    var _in2 *Vector = stack
    _ = _in2
    builder = _in0
    e = _in1
    stack = _in2
    goto TAIL_CALL_START
  } else if (func (_is_3 Sequence) bool {
    return InstanceOf(_is_3, (*LazySequence)(nil))
  }(e)) {
    var _19_lazy *LazySequence
    _ = _19_lazy
    _19_lazy = e.(*LazySequence)
    var _20_boxed Sequence
    _ = _20_boxed
    var _out18 interface{}
    _ = _out18
    _out18 = ((_19_lazy).Box()).Get()
    _20_boxed = Companion_Sequence_.CastTo_(_out18)
    var _in3 *Vector = builder
    _ = _in3
    var _in4 Sequence = _20_boxed
    _ = _in4
    var _in5 *Vector = stack
    _ = _in5
    builder = _in3
    e = _in4
    stack = _in5
    goto TAIL_CALL_START
  } else if (func (_is_4 Sequence) bool {
    return InstanceOf(_is_4, (*ArraySequence)(nil))
  }(e)) {
    var _21_a *ArraySequence
    _ = _21_a
    _21_a = e.(*ArraySequence)
    (builder).Append((_21_a).Values())
    if ((uint32(0)) < (stack.Size)) {
      var _22_next Sequence
      _ = _22_next
      var _out19 interface{}
      _ = _out19
      _out19 = (stack).RemoveLast()
      _22_next = Companion_Sequence_.CastTo_(_out19)
      var _in6 *Vector = builder
      _ = _in6
      var _in7 Sequence = _22_next
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
func (_static *CompanionStruct_Default___) SIZE__T__LIMIT() Int {
  return IntOfInt64(2147483648)
}
func (_static *CompanionStruct_Default___) MIN__SIZE__T__LIMIT() Int {
  return IntOfInt64(128)
}
func (_static *CompanionStruct_Default___) TEN__SIZE() uint32 {
  return uint32(10)
}
func (_static *CompanionStruct_Default___) ONE__SIZE() uint32 {
  return uint32(1)
}
func (_static *CompanionStruct_Default___) SIZE__T__MAX() uint32 {
  return ((Companion_Default___.SIZE__T__LIMIT()).Minus((One))).Uint32()
}
func (_static *CompanionStruct_Default___) TWO__SIZE() uint32 {
  return uint32(2)
}
func (_static *CompanionStruct_Default___) ZERO__SIZE() uint32 {
  return uint32(0)
}
// End of class Default__

// Definition of trait Validatable
type Validatable interface {
  String() string
}
type CompanionStruct_Validatable_ struct {
  TraitID_ *TraitID
}
var Companion_Validatable_ = CompanionStruct_Validatable_ {
  TraitID_: &TraitID{},
}
func (CompanionStruct_Validatable_) CastTo_(x interface{}) Validatable {
  var t Validatable
  t, _ = x.(Validatable)
  return t
}
// End of trait Validatable

// Definition of class Size__t
type Size__t struct {
}

func New_Size__t_() *Size__t {
  _this := Size__t{}

  return &_this
}

type CompanionStruct_Size__t_ struct {
}
var Companion_Size__t_ = CompanionStruct_Size__t_ {
}

func (*Size__t) String() string {
  return "dafny.Size__t"
}
func (_this *CompanionStruct_Size__t_) IntegerRange(lo Int, hi Int) Iterator {
  iter := IntegerRange(lo, hi)
  return func() (interface{}, bool) {
    next, ok := iter()
    if !ok { return uint32(0), false }
    return next.(Int).Uint32(), true
  }
}
func (_this *CompanionStruct_Size__t_) Witness() uint32 {
  return (Zero).Uint32()
}
// End of class Size__t

func Type_Size__t_() TypeDescriptor {
  return type_Size__t_{}
}

type type_Size__t_ struct {
}

func (_this type_Size__t_) Default() interface{} {
  return Companion_Size__t_.Witness()
}

func (_this type_Size__t_) String() string {
  return "dafny.Size__t"
}

// Definition of trait NativeArray
type NativeArray interface {
  String() string
  Length() uint32
  Select(i uint32) interface{}
  Update(i uint32, t interface{})
  UpdateSubarray(start uint32, other ImmutableArray)
  Freeze(size uint32) ImmutableArray
}
type CompanionStruct_NativeArray_ struct {
  TraitID_ *TraitID
}
var Companion_NativeArray_ = CompanionStruct_NativeArray_ {
  TraitID_: &TraitID{},
}
func (CompanionStruct_NativeArray_) CastTo_(x interface{}) NativeArray {
  var t NativeArray
  t, _ = x.(NativeArray)
  return t
}
// End of trait NativeArray

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
      return "dafny_Compile.ArrayCell.Set" + "(" + String(data.Value) + ")"
    }
    case ArrayCell_Unset: {
      return "dafny_Compile.ArrayCell.Unset"
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
      return ok && AreEqual(data1.Value, data2.Value)
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

func Type_ArrayCell_() TypeDescriptor {
  return type_ArrayCell_{}
}

type type_ArrayCell_ struct {
}

func (_this type_ArrayCell_) Default() interface{} {
  return Companion_ArrayCell_.Default();
}

func (_this type_ArrayCell_) String() string {
  return "dafny.ArrayCell"
}
// End of datatype ArrayCell

// Definition of trait ImmutableArray
type ImmutableArray interface {
  String() string
  Length() uint32
  Select(index uint32) interface{}
  Subarray(lo uint32, hi uint32) ImmutableArray
}
type CompanionStruct_ImmutableArray_ struct {
  TraitID_ *TraitID
}
var Companion_ImmutableArray_ = CompanionStruct_ImmutableArray_ {
  TraitID_: &TraitID{},
}
func (CompanionStruct_ImmutableArray_) CastTo_(x interface{}) ImmutableArray {
  var t ImmutableArray
  t, _ = x.(ImmutableArray)
  return t
}
// End of trait ImmutableArray

// Definition of class Vector
type Vector struct {
  Storage NativeArray
  Size uint32
}

func New_Vector_() *Vector {
  _this := Vector{}

  _this.Storage = (NativeArray)(nil)
  _this.Size = Companion_Size__t_.Witness()
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
  return "dafny.Vector"
}

func Type_Vector_(Type_T_ TypeDescriptor) TypeDescriptor {
  return type_Vector_{Type_T_}
}

type type_Vector_ struct {
  Type_T_ TypeDescriptor
}

func (_this type_Vector_) Default() interface{} {
  return (*Vector)(nil)
}

func (_this type_Vector_) String() string {
  return "dafny.Vector"
}
func (_this *Vector) ParentTraits_() []*TraitID {
  return [](*TraitID){Companion_Validatable_.TraitID_};
}
var _ Validatable = &Vector{}
var _ TraitOffspring = &Vector{}
func (_this *Vector) Ctor__(length uint32) {
  {
    var _23_storage NativeArray
    _ = _23_storage
    var _out20 NativeArray
    _ = _out20
    _out20 = Companion_NativeArray_.Make(length)
    _23_storage = _out20
    (_this).Storage = _23_storage
    (_this).Size = uint32(0)
  }
}
func (_this *Vector) Select(index uint32) interface{} {
  {
    return (_this.Storage).Select(index)
  }
}
func (_this *Vector) Last() interface{} {
  {
    return (_this.Storage).Select((_this.Size) - (func () uint32 { return  (uint32(1)) })())
  }
}
func (_this *Vector) AddLast(t interface{}) {
  {
    (_this).EnsureCapacity((_this.Size) + (Companion_Default___.ONE__SIZE()))
    (_this.Storage).Update(_this.Size, t)
    (_this).Size = (_this.Size) + (uint32(1))
  }
}
func (_this *Vector) Max(a uint32, b uint32) uint32 {
  {
    if ((a) < (b)) {
      return b
    } else {
      return a
    }
  }
}
func (_this *Vector) EnsureCapacity(newMinCapacity uint32) {
  {
    if (((_this.Storage).Length()) >= (newMinCapacity)) {
      return
    }
    var _24_newCapacity uint32
    _ = _24_newCapacity
    _24_newCapacity = newMinCapacity
    if (((_this.Storage).Length()) <= ((Companion_Default___.SIZE__T__MAX()) / (Companion_Default___.TWO__SIZE()))) {
      _24_newCapacity = (_this).Max(_24_newCapacity, ((_this.Storage).Length()) * (Companion_Default___.TWO__SIZE()))
    }
    var _25_newStorage NativeArray
    _ = _25_newStorage
    var _out21 NativeArray
    _ = _out21
    _out21 = Companion_NativeArray_.Make(_24_newCapacity)
    _25_newStorage = _out21
    var _26_values ImmutableArray
    _ = _26_values
    var _out22 ImmutableArray
    _ = _out22
    _out22 = (_this.Storage).Freeze(_this.Size)
    _26_values = _out22
    (_25_newStorage).UpdateSubarray(uint32(0), _26_values)
    (_this).Storage = _25_newStorage
  }
}
func (_this *Vector) RemoveLast() interface{} {
  {
    var t interface{} = (interface{})(nil)
    _ = t
    t = (_this.Storage).Select((_this.Size) - (func () uint32 { return  (uint32(1)) })())
    (_this).Size = (_this.Size) - (func () uint32 { return  (uint32(1)) })()
    return t
  }
}
func (_this *Vector) Append(other ImmutableArray) {
  {
    var _27_newSize uint32
    _ = _27_newSize
    _27_newSize = (_this.Size) + ((other).Length())
    (_this).EnsureCapacity(_27_newSize)
    (_this.Storage).UpdateSubarray(_this.Size, other)
    (_this).Size = (_this.Size) + ((other).Length())
  }
}
func (_this *Vector) Freeze() ImmutableArray {
  {
    var ret ImmutableArray = (ImmutableArray)(nil)
    _ = ret
    var _out23 ImmutableArray
    _ = _out23
    _out23 = (_this.Storage).Freeze(_this.Size)
    ret = _out23
    return ret
  }
}
// End of class Vector

// Definition of trait AtomicBox
type AtomicBox interface {
  String() string
  Get() interface{}
  Put(t interface{})
}
type CompanionStruct_AtomicBox_ struct {
  TraitID_ *TraitID
}
var Companion_AtomicBox_ = CompanionStruct_AtomicBox_ {
  TraitID_: &TraitID{},
}
func (CompanionStruct_AtomicBox_) CastTo_(x interface{}) AtomicBox {
  var t AtomicBox
  t, _ = x.(AtomicBox)
  return t
}
// End of trait AtomicBox

// Definition of class ArraySequence
type ArraySequence struct {
  _isString bool
  _values ImmutableArray
}

func New_ArraySequence_() *ArraySequence {
  _this := ArraySequence{}

  _this._isString = false
  _this._values = (ImmutableArray)(nil)
  return &_this
}

type CompanionStruct_ArraySequence_ struct {
}
var Companion_ArraySequence_ = CompanionStruct_ArraySequence_ {
}

func (_this *ArraySequence) Equals(other Sequence) bool {
  return Companion_Sequence_.Equal(_this, other)
}

func (_this *ArraySequence) EqualsGeneric(x interface{}) bool {
  other, ok := x.(Sequence)
  return ok && Companion_Sequence_.Equal(_this, other)
}


func Type_ArraySequence_(Type_T_ TypeDescriptor) TypeDescriptor {
  return type_ArraySequence_{Type_T_}
}

type type_ArraySequence_ struct {
  Type_T_ TypeDescriptor
}

func (_this type_ArraySequence_) Default() interface{} {
  return (*ArraySequence)(nil)
}

func (_this type_ArraySequence_) String() string {
  return "dafny.ArraySequence"
}
func (_this *ArraySequence) ParentTraits_() []*TraitID {
  return [](*TraitID){Companion_Sequence_.TraitID_};
}
var _ Sequence = &ArraySequence{}
var _ TraitOffspring = &ArraySequence{}
func (_this *ArraySequence) SetString() Sequence {
  var _out24 Sequence
  _ = _out24
  _out24 = Companion_Sequence_.SetString(_this)
  return _out24
}
func (_this *ArraySequence) IsString() bool {
  return _this._isString
}
func (_this *ArraySequence) IsString_set_(value bool) {
  _this._isString = value
}
func (_this *ArraySequence) Select(index uint32) interface{} {
  var _out25 interface{}
  _ = _out25
  _out25 = Companion_Sequence_.Select(_this, index)
  return _out25
}
func (_this *ArraySequence) Drop(lo uint32) Sequence {
  var _out26 Sequence
  _ = _out26
  _out26 = Companion_Sequence_.Drop(_this, lo)
  return _out26
}
func (_this *ArraySequence) Take(hi uint32) Sequence {
  var _out27 Sequence
  _ = _out27
  _out27 = Companion_Sequence_.Take(_this, hi)
  return _out27
}
func (_this *ArraySequence) Subsequence(lo uint32, hi uint32) Sequence {
  var _out28 Sequence
  _ = _out28
  _out28 = Companion_Sequence_.Subsequence(_this, lo, hi)
  return _out28
}
func (_this *ArraySequence) Elements() Sequence {
  return Companion_Sequence_.Elements(_this)
}
func (_this *ArraySequence) Ctor__(value ImmutableArray, isString bool) {
  {
    (_this)._values = value
    (_this)._isString = isString
  }
}
func (_this *ArraySequence) Cardinality() uint32 {
  {
    return ((_this).Values()).Length()
  }
}
func (_this *ArraySequence) ToArray() ImmutableArray {
  {
    var ret ImmutableArray = (ImmutableArray)(nil)
    _ = ret
    ret = (_this).Values()
    return ret
    return ret
  }
}
func (_this *ArraySequence) Values() ImmutableArray {
  {
    return _this._values
  }
}
// End of class ArraySequence

// Definition of class ConcatSequence
type ConcatSequence struct {
  _isString bool
  _left Sequence
  _right Sequence
  _length uint32
}

func New_ConcatSequence_() *ConcatSequence {
  _this := ConcatSequence{}

  _this._isString = false
  _this._left = (Sequence)(nil)
  _this._right = (Sequence)(nil)
  _this._length = Companion_Size__t_.Witness()
  return &_this
}

type CompanionStruct_ConcatSequence_ struct {
}
var Companion_ConcatSequence_ = CompanionStruct_ConcatSequence_ {
}

func (_this *ConcatSequence) Equals(other Sequence) bool {
  return Companion_Sequence_.Equal(_this, other)
}

func (_this *ConcatSequence) EqualsGeneric(x interface{}) bool {
  other, ok := x.(Sequence)
  return ok && Companion_Sequence_.Equal(_this, other)
}


func Type_ConcatSequence_(Type_T_ TypeDescriptor) TypeDescriptor {
  return type_ConcatSequence_{Type_T_}
}

type type_ConcatSequence_ struct {
  Type_T_ TypeDescriptor
}

func (_this type_ConcatSequence_) Default() interface{} {
  return (*ConcatSequence)(nil)
}

func (_this type_ConcatSequence_) String() string {
  return "dafny.ConcatSequence"
}
func (_this *ConcatSequence) ParentTraits_() []*TraitID {
  return [](*TraitID){Companion_Sequence_.TraitID_};
}
var _ Sequence = &ConcatSequence{}
var _ TraitOffspring = &ConcatSequence{}
func (_this *ConcatSequence) SetString() Sequence {
  var _out29 Sequence
  _ = _out29
  _out29 = Companion_Sequence_.SetString(_this)
  return _out29
}
func (_this *ConcatSequence) IsString() bool {
  return _this._isString
}
func (_this *ConcatSequence) IsString_set_(value bool) {
  _this._isString = value
}
func (_this *ConcatSequence) Select(index uint32) interface{} {
  var _out30 interface{}
  _ = _out30
  _out30 = Companion_Sequence_.Select(_this, index)
  return _out30
}
func (_this *ConcatSequence) Drop(lo uint32) Sequence {
  var _out31 Sequence
  _ = _out31
  _out31 = Companion_Sequence_.Drop(_this, lo)
  return _out31
}
func (_this *ConcatSequence) Take(hi uint32) Sequence {
  var _out32 Sequence
  _ = _out32
  _out32 = Companion_Sequence_.Take(_this, hi)
  return _out32
}
func (_this *ConcatSequence) Subsequence(lo uint32, hi uint32) Sequence {
  var _out33 Sequence
  _ = _out33
  _out33 = Companion_Sequence_.Subsequence(_this, lo, hi)
  return _out33
}
func (_this *ConcatSequence) Elements() Sequence {
  return Companion_Sequence_.Elements(_this)
}
func (_this *ConcatSequence) Ctor__(left Sequence, right Sequence) {
  {
    (_this)._left = left
    (_this)._right = right
    (_this)._length = ((left).Cardinality()) + ((right).Cardinality())
    (_this)._isString = (left.IsString()) || (right.IsString())
  }
}
func (_this *ConcatSequence) Cardinality() uint32 {
  {
    return (_this).Length()
  }
}
func (_this *ConcatSequence) ToArray() ImmutableArray {
  {
    var ret ImmutableArray = (ImmutableArray)(nil)
    _ = ret
    var _28_builder *Vector
    _ = _28_builder
    var _nw5 *Vector = New_Vector_()
    _ = _nw5
    _nw5.Ctor__((_this).Length())
    _28_builder = _nw5
    var _29_stack *Vector
    _ = _29_stack
    var _nw6 *Vector = New_Vector_()
    _ = _nw6
    _nw6.Ctor__(Companion_Default___.TEN__SIZE())
    _29_stack = _nw6
    Companion_Default___.AppendOptimized(_28_builder, _this, _29_stack)
    var _out34 ImmutableArray
    _ = _out34
    _out34 = (_28_builder).Freeze()
    ret = _out34
    return ret
  }
}
func (_this *ConcatSequence) Left() Sequence {
  {
    return _this._left
  }
}
func (_this *ConcatSequence) Right() Sequence {
  {
    return _this._right
  }
}
func (_this *ConcatSequence) Length() uint32 {
  {
    return _this._length
  }
}
// End of class ConcatSequence

// Definition of class LazySequence
type LazySequence struct {
  _isString bool
  _length uint32
  _box AtomicBox
}

func New_LazySequence_() *LazySequence {
  _this := LazySequence{}

  _this._isString = false
  _this._length = Companion_Size__t_.Witness()
  _this._box = (AtomicBox)(nil)
  return &_this
}

type CompanionStruct_LazySequence_ struct {
}
var Companion_LazySequence_ = CompanionStruct_LazySequence_ {
}

func (_this *LazySequence) Equals(other Sequence) bool {
  return Companion_Sequence_.Equal(_this, other)
}

func (_this *LazySequence) EqualsGeneric(x interface{}) bool {
  other, ok := x.(Sequence)
  return ok && Companion_Sequence_.Equal(_this, other)
}


func Type_LazySequence_(Type_T_ TypeDescriptor) TypeDescriptor {
  return type_LazySequence_{Type_T_}
}

type type_LazySequence_ struct {
  Type_T_ TypeDescriptor
}

func (_this type_LazySequence_) Default() interface{} {
  return (*LazySequence)(nil)
}

func (_this type_LazySequence_) String() string {
  return "dafny.LazySequence"
}
func (_this *LazySequence) ParentTraits_() []*TraitID {
  return [](*TraitID){Companion_Sequence_.TraitID_};
}
var _ Sequence = &LazySequence{}
var _ TraitOffspring = &LazySequence{}
func (_this *LazySequence) SetString() Sequence {
  var _out35 Sequence
  _ = _out35
  _out35 = Companion_Sequence_.SetString(_this)
  return _out35
}
func (_this *LazySequence) IsString() bool {
  return _this._isString
}
func (_this *LazySequence) IsString_set_(value bool) {
  _this._isString = value
}
func (_this *LazySequence) Select(index uint32) interface{} {
  var _out36 interface{}
  _ = _out36
  _out36 = Companion_Sequence_.Select(_this, index)
  return _out36
}
func (_this *LazySequence) Drop(lo uint32) Sequence {
  var _out37 Sequence
  _ = _out37
  _out37 = Companion_Sequence_.Drop(_this, lo)
  return _out37
}
func (_this *LazySequence) Take(hi uint32) Sequence {
  var _out38 Sequence
  _ = _out38
  _out38 = Companion_Sequence_.Take(_this, hi)
  return _out38
}
func (_this *LazySequence) Subsequence(lo uint32, hi uint32) Sequence {
  var _out39 Sequence
  _ = _out39
  _out39 = Companion_Sequence_.Subsequence(_this, lo, hi)
  return _out39
}
func (_this *LazySequence) Elements() Sequence {
  return Companion_Sequence_.Elements(_this)
}
func (_this *LazySequence) Ctor__(wrapped Sequence) {
  {
    var _30_box AtomicBox
    _ = _30_box
    var _out40 AtomicBox
    _ = _out40
    _out40 = Companion_AtomicBox_.Make(wrapped)
    _30_box = _out40
    (_this)._box = _30_box
    (_this)._length = (wrapped).Cardinality()
    (_this)._isString = wrapped.IsString()
  }
}
func (_this *LazySequence) Cardinality() uint32 {
  {
    return (_this).Length()
  }
}
func (_this *LazySequence) ToArray() ImmutableArray {
  {
    var ret ImmutableArray = (ImmutableArray)(nil)
    _ = ret
    var _31_expr Sequence
    _ = _31_expr
    var _out41 interface{}
    _ = _out41
    _out41 = ((_this).Box()).Get()
    _31_expr = Companion_Sequence_.CastTo_(_out41)
    var _out42 ImmutableArray
    _ = _out42
    _out42 = (_31_expr).ToArray()
    ret = _out42
    var _32_arraySeq *ArraySequence
    _ = _32_arraySeq
    var _nw7 *ArraySequence = New_ArraySequence_()
    _ = _nw7
    _nw7.Ctor__(ret, false)
    _32_arraySeq = _nw7
    ((_this).Box()).Put(_32_arraySeq)
    return ret
  }
}
func (_this *LazySequence) Length() uint32 {
  {
    return _this._length
  }
}
func (_this *LazySequence) Box() AtomicBox {
  {
    return _this._box
  }
}
// End of class LazySequence

// Definition of trait Helpers
type Helpers interface {
  String() string
}
type CompanionStruct_Helpers_ struct {
  TraitID_ *TraitID
}
var Companion_Helpers_ = CompanionStruct_Helpers_ {
  TraitID_: &TraitID{},
}
func (CompanionStruct_Helpers_) CastTo_(x interface{}) Helpers {
  var t Helpers
  t, _ = x.(Helpers)
  return t
}
// End of trait Helpers
