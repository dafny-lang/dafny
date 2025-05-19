// Package dafny
// Dafny module dafny compiled into Go

package dafny

type Dummy__ struct{}

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

var Companion_Default___ = CompanionStruct_Default___{}

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
	return [](*TraitID){}
}

var _ TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) SizeAdditionInRange(a uint32, b uint32) bool {
	var _hresult bool = false
	_ = _hresult
	_hresult = (a) <= ((Companion_Default___.SIZE__T__MAX()) - (func() uint32 { return (b) })())
	return _hresult
	return _hresult
}
func (_static *CompanionStruct_Default___) AppendRecursive(builder *Vector, e Sequence) {
	if func(_is_0 Sequence) bool {
		return InstanceOf(_is_0, (*ConcatSequence)(nil))
	}(e) {
		var _0_concat *ConcatSequence
		_ = _0_concat
		_0_concat = e.(*ConcatSequence)
		Companion_Default___.AppendRecursive(builder, (_0_concat).Left())
		Companion_Default___.AppendRecursive(builder, (_0_concat).Right())
	} else if func(_is_1 Sequence) bool {
		return InstanceOf(_is_1, (*LazySequence)(nil))
	}(e) {
		var _1_lazy *LazySequence
		_ = _1_lazy
		_1_lazy = e.(*LazySequence)
		var _2_boxed Sequence
		_ = _2_boxed
		var _out0 interface{}
		_ = _out0
		_out0 = ((_1_lazy).Box()).Get()
		_2_boxed = Companion_Sequence_.CastTo_(Companion_Sequence_.CastTo_(_out0))
		Companion_Default___.AppendRecursive(builder, _2_boxed)
	} else {
		var _3_a ImmutableArray
		_ = _3_a
		var _out1 ImmutableArray
		_ = _out1
		_out1 = Companion_ImmutableArray_.CastTo_((e).ToArray())
		_3_a = Companion_ImmutableArray_.CastTo_(_out1)
		(builder).Append(_3_a)
	}
}
func (_static *CompanionStruct_Default___) AppendOptimized(builder *Vector, e Sequence, stack *Vector) {
	goto TAIL_CALL_START
TAIL_CALL_START:
	if func(_is_2 Sequence) bool {
		return InstanceOf(_is_2, (*ConcatSequence)(nil))
	}(e) {
		var _0_concat *ConcatSequence
		_ = _0_concat
		_0_concat = e.(*ConcatSequence)
		if !(Companion_Default___.SizeAdditionInRange(stack.Size, Companion_Default___.ONE__SIZE())) {
			panic("dafnyRuntime.dfy(754,6): " + (SeqOfString("expectation violation")).String())
		}
		(stack).AddLast((_0_concat).Right())
		var _in0 *Vector = builder
		_ = _in0
		var _in1 Sequence = (_0_concat).Left()
		_ = _in1
		var _in2 *Vector = stack
		_ = _in2
		builder = _in0
		e = _in1
		stack = _in2
		goto TAIL_CALL_START
	} else if func(_is_3 Sequence) bool {
		return InstanceOf(_is_3, (*LazySequence)(nil))
	}(e) {
		var _1_lazy *LazySequence
		_ = _1_lazy
		_1_lazy = e.(*LazySequence)
		var _2_boxed Sequence
		_ = _2_boxed
		var _out0 interface{}
		_ = _out0
		_out0 = ((_1_lazy).Box()).Get()
		_2_boxed = Companion_Sequence_.CastTo_(Companion_Sequence_.CastTo_(_out0))
		var _in3 *Vector = builder
		_ = _in3
		var _in4 Sequence = _2_boxed
		_ = _in4
		var _in5 *Vector = stack
		_ = _in5
		builder = _in3
		e = _in4
		stack = _in5
		goto TAIL_CALL_START
	} else if func(_is_4 Sequence) bool {
		return InstanceOf(_is_4, (*ArraySequence)(nil))
	}(e) {
		var _3_a *ArraySequence
		_ = _3_a
		_3_a = e.(*ArraySequence)
		(builder).Append((_3_a).Values())
		if (uint32(0)) < (stack.Size) {
			var _4_next Sequence
			_ = _4_next
			var _out1 interface{}
			_ = _out1
			_out1 = (stack).RemoveLast()
			_4_next = Companion_Sequence_.CastTo_(Companion_Sequence_.CastTo_(_out1))
			var _in6 *Vector = builder
			_ = _in6
			var _in7 Sequence = _4_next
			_ = _in7
			var _in8 *Vector = stack
			_ = _in8
			builder = _in6
			e = _in7
			stack = _in8
			goto TAIL_CALL_START
		}
	} else {
		if !(false) {
			panic("dafnyRuntime.dfy(777,6): " + (SeqOfString("Unsupported Sequence implementation")).String())
		}
	}
}
func (_static *CompanionStruct_Default___) SIZE__T__LIMIT() Int {
	return IntOfInt64(2147483648)
}
func (_static *CompanionStruct_Default___) SIZE__T__MAX() uint32 {
	return ((Companion_Default___.SIZE__T__LIMIT()).Minus(One)).Uint32()
}
func (_static *CompanionStruct_Default___) ZERO__SIZE() uint32 {
	return uint32(0)
}
func (_static *CompanionStruct_Default___) ONE__SIZE() uint32 {
	return uint32(1)
}
func (_static *CompanionStruct_Default___) TWO__SIZE() uint32 {
	return uint32(2)
}
func (_static *CompanionStruct_Default___) TEN__SIZE() uint32 {
	return uint32(10)
}

// End of class Default__

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
		(_this).IsString_set_(true)
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
		var _out0 Sequence
		_ = _out0
		_out0 = (_this).Subsequence(lo, (_this).Cardinality())
		ret = _out0
		return ret
	}
}
func (_static *CompanionStruct_Sequence_) Take(_this Sequence, hi uint32) Sequence {
	{
		var ret Sequence = (Sequence)(nil)
		_ = ret
		var _out0 Sequence
		_ = _out0
		_out0 = (_this).Subsequence(uint32(0), hi)
		ret = _out0
		return ret
	}
}
func (_static *CompanionStruct_Sequence_) Subsequence(_this Sequence, lo uint32, hi uint32) Sequence {
	{
		var ret Sequence = (Sequence)(nil)
		_ = ret
		var _0_a ImmutableArray
		_ = _0_a
		var _out0 ImmutableArray
		_ = _out0
		_out0 = (_this).ToArray()
		_0_a = _out0
		var _1_subarray ImmutableArray
		_ = _1_subarray
		var _out1 ImmutableArray
		_ = _out1
		_out1 = Companion_ImmutableArray_.CastTo_((_0_a).Subarray(lo, hi))
		_1_subarray = Companion_ImmutableArray_.CastTo_(_out1)
		var _nw0 *ArraySequence = New_ArraySequence_()
		_ = _nw0
		_nw0.Ctor__(_1_subarray, false)
		ret = _nw0
		return ret
	}
}
func (_static *CompanionStruct_Sequence_) Elements(_this Sequence) Sequence {
	{
		return _this
	}
}
func (_static *CompanionStruct_Sequence_) Create(cardinality uint32, initFn func(uint32) interface{}) Sequence {
	var ret Sequence = (Sequence)(nil)
	_ = ret
	var _0_a NativeArray
	_ = _0_a
	var _out0 NativeArray
	_ = _out0
	_out0 = Companion_NativeArray_.CastTo_(Companion_NativeArray_.MakeWithInit(cardinality, func(coer0 func(uint32) interface{}) func(uint32) interface{} {
		return func(arg0 uint32) interface{} {
			return coer0(arg0)
		}
	}(initFn)))
	_0_a = Companion_NativeArray_.CastTo_(_out0)
	var _1_frozen ImmutableArray
	_ = _1_frozen
	var _out1 ImmutableArray
	_ = _out1
	_out1 = Companion_ImmutableArray_.CastTo_((_0_a).Freeze(cardinality))
	_1_frozen = Companion_ImmutableArray_.CastTo_(_out1)
	var _nw0 *ArraySequence = New_ArraySequence_()
	_ = _nw0
	_nw0.Ctor__(_1_frozen, false)
	ret = _nw0
	return ret
}
func (_static *CompanionStruct_Sequence_) Equal(left Sequence, right Sequence) bool {
	var ret bool = false
	_ = ret
	if ((left).Cardinality()) != ((right).Cardinality()) /* dircomp */ {
		ret = false
		return ret
	}
	var _out0 bool
	_ = _out0
	_out0 = Companion_Sequence_.EqualUpTo(left, right, (left).Cardinality())
	ret = _out0
	return ret
}
func (_static *CompanionStruct_Sequence_) IsPrefixOf(left Sequence, right Sequence) bool {
	var ret bool = false
	_ = ret
	if ((right).Cardinality()) < ((left).Cardinality()) {
		ret = false
		return ret
	}
	var _out0 bool
	_ = _out0
	_out0 = Companion_Sequence_.EqualUpTo(left, right, (left).Cardinality())
	ret = _out0
	return ret
}
func (_static *CompanionStruct_Sequence_) IsProperPrefixOf(left Sequence, right Sequence) bool {
	var ret bool = false
	_ = ret
	if ((right).Cardinality()) <= ((left).Cardinality()) {
		ret = false
		return ret
	}
	var _out0 bool
	_ = _out0
	_out0 = Companion_Sequence_.EqualUpTo(left, right, (left).Cardinality())
	ret = _out0
	return ret
}
func (_static *CompanionStruct_Sequence_) Contains(s Sequence, t interface{}) bool {
	var _hresult bool = false
	_ = _hresult
	var _hi0 uint32 = (s).Cardinality()
	_ = _hi0
	for _0_i := Companion_Default___.ZERO__SIZE(); _0_i < _hi0; _0_i++ {
		var _1_element interface{}
		_ = _1_element
		var _out0 interface{}
		_ = _out0
		_out0 = (s).Select(_0_i)
		_1_element = _out0
		if AreEqual(_1_element, t) {
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
	var _0_a ImmutableArray
	_ = _0_a
	var _out0 ImmutableArray
	_ = _out0
	_out0 = Companion_ImmutableArray_.CastTo_((s).ToArray())
	_0_a = Companion_ImmutableArray_.CastTo_(_out0)
	var _1_newValue NativeArray
	_ = _1_newValue
	var _out1 NativeArray
	_ = _out1
	_out1 = Companion_NativeArray_.CastTo_(Companion_NativeArray_.Copy(_0_a))
	_1_newValue = Companion_NativeArray_.CastTo_(_out1)
	(_1_newValue).Update(i, t)
	var _2_newValueFrozen ImmutableArray
	_ = _2_newValueFrozen
	var _out2 ImmutableArray
	_ = _out2
	_out2 = Companion_ImmutableArray_.CastTo_((_1_newValue).Freeze((_1_newValue).Length()))
	_2_newValueFrozen = Companion_ImmutableArray_.CastTo_(_out2)
	var _nw0 *ArraySequence = New_ArraySequence_()
	_ = _nw0
	_nw0.Ctor__(_2_newValueFrozen, false)
	ret = _nw0
	return ret
}
func (_static *CompanionStruct_Sequence_) Concatenate(left Sequence, right Sequence) Sequence {
	var ret Sequence = (Sequence)(nil)
	_ = ret
	if !(Companion_Default___.SizeAdditionInRange((left).Cardinality(), (right).Cardinality())) {
		panic("dafnyRuntime.dfy(582,6): " + (Companion_Sequence_.Concatenate(Companion_Sequence_.Concatenate(SeqOfString("Concatenation result cardinality would be larger than the maximum ("), Companion_Helpers_.DafnyValueToDafnyString(Companion_Default___.SIZE__T__MAX())), SeqOfString(")"))).String())
	}
	var _0_left_k Sequence
	_ = _0_left_k
	_0_left_k = left
	if func(_is_5 Sequence) bool {
		return InstanceOf(_is_5, (*LazySequence)(nil))
	}(left) {
		var _1_lazyLeft *LazySequence
		_ = _1_lazyLeft
		_1_lazyLeft = left.(*LazySequence)
		var _out0 interface{}
		_ = _out0
		_out0 = ((_1_lazyLeft).Box()).Get()
		_0_left_k = Companion_Sequence_.CastTo_(Companion_Sequence_.CastTo_(_out0))
	}
	var _2_right_k Sequence
	_ = _2_right_k
	_2_right_k = right
	if func(_is_6 Sequence) bool {
		return InstanceOf(_is_6, (*LazySequence)(nil))
	}(right) {
		var _3_lazyRight *LazySequence
		_ = _3_lazyRight
		_3_lazyRight = right.(*LazySequence)
		var _out1 interface{}
		_ = _out1
		_out1 = ((_3_lazyRight).Box()).Get()
		_2_right_k = Companion_Sequence_.CastTo_(Companion_Sequence_.CastTo_(_out1))
	}
	var _4_c *ConcatSequence
	_ = _4_c
	var _nw0 *ConcatSequence = New_ConcatSequence_()
	_ = _nw0
	_nw0.Ctor__(_0_left_k, _2_right_k)
	_4_c = _nw0
	var _nw1 *LazySequence = New_LazySequence_()
	_ = _nw1
	_nw1.Ctor__(_4_c)
	ret = _nw1
	return ret
}

type CompanionStruct_Sequence_ struct {
	TraitID_ *TraitID
}

var Companion_Sequence_ = CompanionStruct_Sequence_{
	TraitID_: &TraitID{},
}

func (CompanionStruct_Sequence_) CastTo_(x interface{}) Sequence {
	var t Sequence
	t, _ = x.(Sequence)
	return t
}

// End of trait Sequence

// Definition of trait Validatable
type Validatable interface {
	String() string
}
type CompanionStruct_Validatable_ struct {
	TraitID_ *TraitID
}

var Companion_Validatable_ = CompanionStruct_Validatable_{
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

var Companion_Size__t_ = CompanionStruct_Size__t_{}

func (*Size__t) String() string {
	return "dafny.Size__t"
}
func (_this *Size__t) ParentTraits_() []*TraitID {
	return [](*TraitID){}
}

var _ TraitOffspring = &Size__t{}

func (_this *CompanionStruct_Size__t_) IntegerRange(lo Int, hi Int) Iterator {
	iter := IntegerRange(lo, hi)
	return func() (interface{}, bool) {
		next, ok := iter()
		if !ok {
			return uint32(0), false
		}
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
func (_this *CompanionStruct_Size__t_) Is_(__source uint32) bool {
	var _0_x Int = IntOfUint32(__source)
	_ = _0_x
	return ((_0_x).Sign() != -1) && ((_0_x).Cmp(Companion_Default___.SIZE__T__LIMIT()) < 0)
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

var Companion_NativeArray_ = CompanionStruct_NativeArray_{
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

func (_this ArrayCell) Get_() Data_ArrayCell_ {
	return _this.Data_ArrayCell_
}

type Data_ArrayCell_ interface {
	isArrayCell()
}

type CompanionStruct_ArrayCell_ struct {
}

var Companion_ArrayCell_ = CompanionStruct_ArrayCell_{}

type ArrayCell_Set struct {
	Value interface{}
}

func (ArrayCell_Set) isArrayCell() {}

func (CompanionStruct_ArrayCell_) Create_Set_(Value interface{}) ArrayCell {
	return ArrayCell{ArrayCell_Set{Value}}
}

func (_this ArrayCell) Is_Set() bool {
	_, ok := _this.Get_().(ArrayCell_Set)
	return ok
}

type ArrayCell_Unset struct {
}

func (ArrayCell_Unset) isArrayCell() {}

func (CompanionStruct_ArrayCell_) Create_Unset_() ArrayCell {
	return ArrayCell{ArrayCell_Unset{}}
}

func (_this ArrayCell) Is_Unset() bool {
	_, ok := _this.Get_().(ArrayCell_Unset)
	return ok
}

func (CompanionStruct_ArrayCell_) Default() ArrayCell {
	return Companion_ArrayCell_.Create_Unset_()
}

func (_this ArrayCell) Dtor_value() interface{} {
	return _this.Get_().(ArrayCell_Set).Value
}

func (_this ArrayCell) String() string {
	switch data := _this.Get_().(type) {
	case nil:
		return "null"
	case ArrayCell_Set:
		{
			return "DafnyGo.ArrayCell.Set" + "(" + String(data.Value) + ")"
		}
	case ArrayCell_Unset:
		{
			return "DafnyGo.ArrayCell.Unset"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this ArrayCell) Equals(other ArrayCell) bool {
	switch data1 := _this.Get_().(type) {
	case ArrayCell_Set:
		{
			data2, ok := other.Get_().(ArrayCell_Set)
			return ok && AreEqual(data1.Value, data2.Value)
		}
	case ArrayCell_Unset:
		{
			_, ok := other.Get_().(ArrayCell_Unset)
			return ok
		}
	default:
		{
			return false // unexpected
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
	return Companion_ArrayCell_.Default()
}

func (_this type_ArrayCell_) String() string {
	return "dafny.ArrayCell"
}
func (_this ArrayCell) ParentTraits_() []*TraitID {
	return [](*TraitID){}
}

var _ TraitOffspring = ArrayCell{}

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

var Companion_ImmutableArray_ = CompanionStruct_ImmutableArray_{
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
	Size    uint32
}

func New_Vector_() *Vector {
	_this := Vector{}

	_this.Storage = (NativeArray)(nil)
	_this.Size = Companion_Size__t_.Witness()
	return &_this
}

type CompanionStruct_Vector_ struct {
}

var Companion_Vector_ = CompanionStruct_Vector_{}

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
	return [](*TraitID){Companion_Validatable_.TraitID_}
}

var _ Validatable = &Vector{}
var _ TraitOffspring = &Vector{}

func (_this *Vector) Ctor__(length uint32) {
	{
		var _0_storage NativeArray
		_ = _0_storage
		var _out0 NativeArray
		_ = _out0
		_out0 = Companion_NativeArray_.CastTo_(Companion_NativeArray_.Make(length))
		_0_storage = Companion_NativeArray_.CastTo_(_out0)
		(_this).Storage = _0_storage
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
		return (_this.Storage).Select((_this.Size) - (func() uint32 { return (uint32(1)) })())
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
		if (a) < (b) {
			return b
		} else {
			return a
		}
	}
}
func (_this *Vector) EnsureCapacity(newMinCapacity uint32) {
	{
		if ((_this.Storage).Length()) >= (newMinCapacity) {
			return
		}
		var _0_newCapacity uint32
		_ = _0_newCapacity
		_0_newCapacity = newMinCapacity
		if ((_this.Storage).Length()) <= ((Companion_Default___.SIZE__T__MAX()) / (Companion_Default___.TWO__SIZE())) {
			_0_newCapacity = (_this).Max(_0_newCapacity, ((_this.Storage).Length())*(Companion_Default___.TWO__SIZE()))
		}
		var _1_newStorage NativeArray
		_ = _1_newStorage
		var _out0 NativeArray
		_ = _out0
		_out0 = Companion_NativeArray_.CastTo_(Companion_NativeArray_.Make(_0_newCapacity))
		_1_newStorage = Companion_NativeArray_.CastTo_(_out0)
		var _2_values ImmutableArray
		_ = _2_values
		var _out1 ImmutableArray
		_ = _out1
		_out1 = Companion_ImmutableArray_.CastTo_((_this.Storage).Freeze(_this.Size))
		_2_values = Companion_ImmutableArray_.CastTo_(_out1)
		(_1_newStorage).UpdateSubarray(uint32(0), _2_values)
		(_this).Storage = _1_newStorage
	}
}
func (_this *Vector) RemoveLast() interface{} {
	{
		var t interface{} = (interface{})(nil)
		_ = t
		t = (_this.Storage).Select((_this.Size) - (func() uint32 { return (uint32(1)) })())
		(_this).Size = (_this.Size) - (func() uint32 { return (uint32(1)) })()
		return t
	}
}
func (_this *Vector) Append(other ImmutableArray) {
	{
		var _0_newSize uint32
		_ = _0_newSize
		_0_newSize = (_this.Size) + ((other).Length())
		(_this).EnsureCapacity(_0_newSize)
		(_this.Storage).UpdateSubarray(_this.Size, other)
		(_this).Size = (_this.Size) + ((other).Length())
	}
}
func (_this *Vector) Freeze() ImmutableArray {
	{
		var ret ImmutableArray = (ImmutableArray)(nil)
		_ = ret
		var _out0 ImmutableArray
		_ = _out0
		_out0 = Companion_ImmutableArray_.CastTo_((_this.Storage).Freeze(_this.Size))
		ret = Companion_ImmutableArray_.CastTo_(_out0)
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

var Companion_AtomicBox_ = CompanionStruct_AtomicBox_{
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
	_values   ImmutableArray
}

func New_ArraySequence_() *ArraySequence {
	_this := ArraySequence{}

	_this._isString = false
	_this._values = (ImmutableArray)(nil)
	return &_this
}

type CompanionStruct_ArraySequence_ struct {
}

var Companion_ArraySequence_ = CompanionStruct_ArraySequence_{}

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
	return [](*TraitID){Companion_Sequence_.TraitID_}
}

var _ Sequence = &ArraySequence{}
var _ TraitOffspring = &ArraySequence{}

func (_this *ArraySequence) Drop(lo uint32) Sequence {
	var _out1 Sequence
	_ = _out1
	_out1 = Companion_Sequence_.Drop(_this, lo)
	return _out1
}
func (_this *ArraySequence) Elements() Sequence {
	return Companion_Sequence_.Elements(_this)
}
func (_this *ArraySequence) IsString() bool {
	return _this._isString
}
func (_this *ArraySequence) IsString_set_(value bool) {
	_this._isString = value
}
func (_this *ArraySequence) Select(index uint32) interface{} {
	var _out1 interface{}
	_ = _out1
	_out1 = Companion_Sequence_.Select(_this, index)
	return _out1
}
func (_this *ArraySequence) SetString() Sequence {
	var _out0 Sequence
	_ = _out0
	_out0 = Companion_Sequence_.SetString(_this)
	return _out0
}
func (_this *ArraySequence) Subsequence(lo uint32, hi uint32) Sequence {
	var _out2 Sequence
	_ = _out2
	_out2 = Companion_Sequence_.Subsequence(_this, lo, hi)
	return _out2
}
func (_this *ArraySequence) Take(hi uint32) Sequence {
	var _out1 Sequence
	_ = _out1
	_out1 = Companion_Sequence_.Take(_this, hi)
	return _out1
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
	_left     Sequence
	_right    Sequence
	_length   uint32
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

var Companion_ConcatSequence_ = CompanionStruct_ConcatSequence_{}

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
	return [](*TraitID){Companion_Sequence_.TraitID_}
}

var _ Sequence = &ConcatSequence{}
var _ TraitOffspring = &ConcatSequence{}

func (_this *ConcatSequence) Drop(lo uint32) Sequence {
	var _out2 Sequence
	_ = _out2
	_out2 = Companion_Sequence_.Drop(_this, lo)
	return _out2
}
func (_this *ConcatSequence) Elements() Sequence {
	return Companion_Sequence_.Elements(_this)
}
func (_this *ConcatSequence) IsString() bool {
	return _this._isString
}
func (_this *ConcatSequence) IsString_set_(value bool) {
	_this._isString = value
}
func (_this *ConcatSequence) Select(index uint32) interface{} {
	var _out2 interface{}
	_ = _out2
	_out2 = Companion_Sequence_.Select(_this, index)
	return _out2
}
func (_this *ConcatSequence) SetString() Sequence {
	var _out1 Sequence
	_ = _out1
	_out1 = Companion_Sequence_.SetString(_this)
	return _out1
}
func (_this *ConcatSequence) Subsequence(lo uint32, hi uint32) Sequence {
	var _out3 Sequence
	_ = _out3
	_out3 = Companion_Sequence_.Subsequence(_this, lo, hi)
	return _out3
}
func (_this *ConcatSequence) Take(hi uint32) Sequence {
	var _out2 Sequence
	_ = _out2
	_out2 = Companion_Sequence_.Take(_this, hi)
	return _out2
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
		var _0_builder *Vector
		_ = _0_builder
		var _nw0 *Vector = New_Vector_()
		_ = _nw0
		_nw0.Ctor__((_this).Length())
		_0_builder = _nw0
		var _1_stack *Vector
		_ = _1_stack
		var _nw1 *Vector = New_Vector_()
		_ = _nw1
		_nw1.Ctor__(Companion_Default___.TEN__SIZE())
		_1_stack = _nw1
		Companion_Default___.AppendOptimized(_0_builder, _this, _1_stack)
		var _out0 ImmutableArray
		_ = _out0
		_out0 = Companion_ImmutableArray_.CastTo_((_0_builder).Freeze())
		ret = Companion_ImmutableArray_.CastTo_(_out0)
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
	_length   uint32
	_box      AtomicBox
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

var Companion_LazySequence_ = CompanionStruct_LazySequence_{}

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
	return [](*TraitID){Companion_Sequence_.TraitID_}
}

var _ Sequence = &LazySequence{}
var _ TraitOffspring = &LazySequence{}

func (_this *LazySequence) Drop(lo uint32) Sequence {
	var _out3 Sequence
	_ = _out3
	_out3 = Companion_Sequence_.Drop(_this, lo)
	return _out3
}
func (_this *LazySequence) Elements() Sequence {
	return Companion_Sequence_.Elements(_this)
}
func (_this *LazySequence) IsString() bool {
	return _this._isString
}
func (_this *LazySequence) IsString_set_(value bool) {
	_this._isString = value
}
func (_this *LazySequence) Select(index uint32) interface{} {
	var _out3 interface{}
	_ = _out3
	_out3 = Companion_Sequence_.Select(_this, index)
	return _out3
}
func (_this *LazySequence) SetString() Sequence {
	var _out2 Sequence
	_ = _out2
	_out2 = Companion_Sequence_.SetString(_this)
	return _out2
}
func (_this *LazySequence) Subsequence(lo uint32, hi uint32) Sequence {
	var _out4 Sequence
	_ = _out4
	_out4 = Companion_Sequence_.Subsequence(_this, lo, hi)
	return _out4
}
func (_this *LazySequence) Take(hi uint32) Sequence {
	var _out3 Sequence
	_ = _out3
	_out3 = Companion_Sequence_.Take(_this, hi)
	return _out3
}
func (_this *LazySequence) Ctor__(wrapped Sequence) {
	{
		var _0_box AtomicBox
		_ = _0_box
		var _out0 AtomicBox
		_ = _out0
		_out0 = Companion_AtomicBox_.CastTo_(Companion_AtomicBox_.Make(wrapped))
		_0_box = Companion_AtomicBox_.CastTo_(_out0)
		(_this)._box = _0_box
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
		var _0_expr Sequence
		_ = _0_expr
		var _out0 interface{}
		_ = _out0
		_out0 = ((_this).Box()).Get()
		_0_expr = Companion_Sequence_.CastTo_(Companion_Sequence_.CastTo_(_out0))
		if func(_is_7 Sequence) bool {
			return InstanceOf(_is_7, (*ArraySequence)(nil))
		}(_0_expr) {
			ret = (_0_expr.(*ArraySequence)).Values()
			return ret
		}
		var _out1 ImmutableArray
		_ = _out1
		_out1 = Companion_ImmutableArray_.CastTo_((_0_expr).ToArray())
		ret = Companion_ImmutableArray_.CastTo_(_out1)
		var _1_arraySeq *ArraySequence
		_ = _1_arraySeq
		var _nw0 *ArraySequence = New_ArraySequence_()
		_ = _nw0
		_nw0.Ctor__(ret, false)
		_1_arraySeq = _nw0
		((_this).Box()).Put(_1_arraySeq)
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

var Companion_Helpers_ = CompanionStruct_Helpers_{
	TraitID_: &TraitID{},
}

func (CompanionStruct_Helpers_) CastTo_(x interface{}) Helpers {
	var t Helpers
	t, _ = x.(Helpers)
	return t
}

// End of trait Helpers
