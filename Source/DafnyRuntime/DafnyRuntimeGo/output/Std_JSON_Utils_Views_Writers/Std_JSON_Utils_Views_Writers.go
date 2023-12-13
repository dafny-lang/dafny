// Package Std_JSON_Utils_Views_Writers
// Dafny module Std_JSON_Utils_Views_Writers compiled into Go

package Std_JSON_Utils_Views_Writers

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
  Std_DynamicArray "Std_DynamicArray"
  Std_FileIO "Std_FileIO"
  Std_Arithmetic_GeneralInternals "Std_Arithmetic_GeneralInternals"
  Std_Arithmetic_MulInternalsNonlinear "Std_Arithmetic_MulInternalsNonlinear"
  Std_Arithmetic_MulInternals "Std_Arithmetic_MulInternals"
  Std_Arithmetic_Mul "Std_Arithmetic_Mul"
  Std_Arithmetic_ModInternalsNonlinear "Std_Arithmetic_ModInternalsNonlinear"
  Std_Arithmetic_DivInternalsNonlinear "Std_Arithmetic_DivInternalsNonlinear"
  Std_Arithmetic_ModInternals "Std_Arithmetic_ModInternals"
  Std_Arithmetic_DivInternals "Std_Arithmetic_DivInternals"
  Std_Arithmetic_DivMod "Std_Arithmetic_DivMod"
  Std_Arithmetic_Power "Std_Arithmetic_Power"
  Std_Arithmetic_Logarithm "Std_Arithmetic_Logarithm"
  Std_Arithmetic_Power2 "Std_Arithmetic_Power2"
  Std_Arithmetic "Std_Arithmetic"
  Std_Strings_HexConversion "Std_Strings_HexConversion"
  Std_Strings_DecimalConversion "Std_Strings_DecimalConversion"
  Std_Strings_CharStrEscaping "Std_Strings_CharStrEscaping"
  Std_Strings "Std_Strings"
  Std_Unicode_Base "Std_Unicode_Base"
  Std_Unicode_Utf8EncodingForm "Std_Unicode_Utf8EncodingForm"
  Std_Unicode_Utf16EncodingForm "Std_Unicode_Utf16EncodingForm"
  Std_Unicode_UnicodeStringsWithUnicodeChar "Std_Unicode_UnicodeStringsWithUnicodeChar"
  Std_Unicode_Utf8EncodingScheme "Std_Unicode_Utf8EncodingScheme"
  Std_Unicode "Std_Unicode"
  Std_JSON_Values "Std_JSON_Values"
  Std_JSON_Errors "Std_JSON_Errors"
  Std_JSON_Spec "Std_JSON_Spec"
  Std_JSON_Utils_Views_Core "Std_JSON_Utils_Views_Core"
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
var _ Std_DynamicArray.Dummy__
var _ Std_FileIO.Dummy__
var _ Std_Arithmetic_GeneralInternals.Dummy__
var _ Std_Arithmetic_MulInternalsNonlinear.Dummy__
var _ Std_Arithmetic_MulInternals.Dummy__
var _ Std_Arithmetic_Mul.Dummy__
var _ Std_Arithmetic_ModInternalsNonlinear.Dummy__
var _ Std_Arithmetic_DivInternalsNonlinear.Dummy__
var _ Std_Arithmetic_ModInternals.Dummy__
var _ Std_Arithmetic_DivInternals.Dummy__
var _ Std_Arithmetic_DivMod.Dummy__
var _ Std_Arithmetic_Power.Dummy__
var _ Std_Arithmetic_Logarithm.Dummy__
var _ Std_Arithmetic_Power2.Dummy__
var _ Std_Arithmetic.Dummy__
var _ Std_Strings_HexConversion.Dummy__
var _ Std_Strings_DecimalConversion.Dummy__
var _ Std_Strings_CharStrEscaping.Dummy__
var _ Std_Strings.Dummy__
var _ Std_Unicode_Base.Dummy__
var _ Std_Unicode_Utf8EncodingForm.Dummy__
var _ Std_Unicode_Utf16EncodingForm.Dummy__
var _ Std_Unicode_UnicodeStringsWithUnicodeChar.Dummy__
var _ Std_Unicode_Utf8EncodingScheme.Dummy__
var _ Std_Unicode.Dummy__
var _ Std_JSON_Values.Dummy__
var _ Std_JSON_Errors.Dummy__
var _ Std_JSON_Spec.Dummy__
var _ Std_JSON_Utils_Views_Core.Dummy__

type Dummy__ struct{}



// Definition of datatype Chain
type Chain struct {
  Data_Chain_
}

func (_this Chain) Get_() Data_Chain_ {
  return _this.Data_Chain_
}

type Data_Chain_ interface {
  isChain()
}

type CompanionStruct_Chain_ struct {
}
var Companion_Chain_ = CompanionStruct_Chain_ {
}

type Chain_Empty struct {
}

func (Chain_Empty) isChain() {}

func (CompanionStruct_Chain_) Create_Empty_() Chain {
  return Chain{Chain_Empty{}}
}

func (_this Chain) Is_Empty() bool {
  _, ok := _this.Get_().(Chain_Empty)
  return ok
}

type Chain_Chain struct {
  Previous Chain
  V Std_JSON_Utils_Views_Core.View__
}

func (Chain_Chain) isChain() {}

func (CompanionStruct_Chain_) Create_Chain_(Previous Chain, V Std_JSON_Utils_Views_Core.View__) Chain {
  return Chain{Chain_Chain{Previous, V}}
}

func (_this Chain) Is_Chain() bool {
  _, ok := _this.Get_().(Chain_Chain)
  return ok
}

func (CompanionStruct_Chain_) Default() Chain {
  return Companion_Chain_.Create_Empty_()
}

func (_this Chain) Dtor_previous() Chain {
  return _this.Get_().(Chain_Chain).Previous
}

func (_this Chain) Dtor_v() Std_JSON_Utils_Views_Core.View__ {
  return _this.Get_().(Chain_Chain).V
}

func (_this Chain) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case Chain_Empty: {
      return "Writers.Chain.Empty"
    }
    case Chain_Chain: {
      return "Writers.Chain.Chain" + "(" + _dafny.String(data.Previous) + ", " + _dafny.String(data.V) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this Chain) Equals(other Chain) bool {
  switch data1 := _this.Get_().(type) {
    case Chain_Empty: {
      _, ok := other.Get_().(Chain_Empty)
      return ok
    }
    case Chain_Chain: {
      data2, ok := other.Get_().(Chain_Chain)
      return ok && data1.Previous.Equals(data2.Previous) && data1.V.Equals(data2.V)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this Chain) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(Chain)
  return ok && _this.Equals(typed)
}

func Type_Chain_() _dafny.TypeDescriptor {
  return type_Chain_{}
}

type type_Chain_ struct {
}

func (_this type_Chain_) Default() interface{} {
  return Companion_Chain_.Default();
}

func (_this type_Chain_) String() string {
  return "Std_JSON_Utils_Views_Writers.Chain"
}
func (_this Chain) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Chain{}

func (_this Chain) Length() _dafny.Int {
  {
    var _355___accumulator _dafny.Int = _dafny.Zero
    _ = _355___accumulator
    goto TAIL_CALL_START
    TAIL_CALL_START:
    if ((_this).Is_Empty()) {
      return (_dafny.Zero).Plus(_355___accumulator)
    } else {
      _355___accumulator = (_dafny.IntOfUint32(((_this).Dtor_v()).Length())).Plus(_355___accumulator)
      var _in64 Chain = (_this).Dtor_previous()
      _ = _in64
      _this = _in64
      
      goto TAIL_CALL_START
    }
  }
}
func (_this Chain) Count() _dafny.Int {
  {
    var _356___accumulator _dafny.Int = _dafny.Zero
    _ = _356___accumulator
    goto TAIL_CALL_START
    TAIL_CALL_START:
    if ((_this).Is_Empty()) {
      return (_dafny.Zero).Plus(_356___accumulator)
    } else {
      _356___accumulator = (_dafny.One).Plus(_356___accumulator)
      var _in65 Chain = (_this).Dtor_previous()
      _ = _in65
      _this = _in65
      
      goto TAIL_CALL_START
    }
  }
}
func (_this Chain) Bytes() _dafny.Sequence {
  {
    var _357___accumulator _dafny.Sequence = _dafny.SeqOf()
    _ = _357___accumulator
    goto TAIL_CALL_START
    TAIL_CALL_START:
    if ((_this).Is_Empty()) {
      return _dafny.Companion_Sequence_.Concatenate(_dafny.SeqOf(), _357___accumulator)
    } else {
      _357___accumulator = _dafny.Companion_Sequence_.Concatenate(((_this).Dtor_v()).Bytes(), _357___accumulator)
      var _in66 Chain = (_this).Dtor_previous()
      _ = _in66
      _this = _in66
      
      goto TAIL_CALL_START
    }
  }
}
func (_this Chain) Append(v_k Std_JSON_Utils_Views_Core.View__) Chain {
  {
    if (((_this).Is_Chain()) && (Std_JSON_Utils_Views_Core.Companion_Default___.Adjacent((_this).Dtor_v(), v_k))) {
      return Companion_Chain_.Create_Chain_((_this).Dtor_previous(), Std_JSON_Utils_Views_Core.Companion_Default___.Merge((_this).Dtor_v(), v_k))
    } else {
      return Companion_Chain_.Create_Chain_(_this, v_k)
    }
  }
}
func (_this Chain) CopyTo(dest _dafny.Array, end uint32) {
  {
    goto TAIL_CALL_START
    TAIL_CALL_START:
    if ((_this).Is_Chain()) {
      var _358_end uint32
      _ = _358_end
      _358_end = (end) - (func () uint32 { return  (((_this).Dtor_v()).Length()) })()
      ((_this).Dtor_v()).CopyTo(dest, _358_end)
      var _in67 Chain = (_this).Dtor_previous()
      _ = _in67
      var _in68 _dafny.Array = dest
      _ = _in68
      var _in69 uint32 = _358_end
      _ = _in69
      _this = _in67
      
      dest = _in68
      end = _in69
      goto TAIL_CALL_START
    }
  }
}
// End of datatype Chain

// Definition of class Writer
type Writer struct {
}

func New_Writer_() *Writer {
  _this := Writer{}

  return &_this
}

type CompanionStruct_Writer_ struct {
}
var Companion_Writer_ = CompanionStruct_Writer_ {
}

func (*Writer) String() string {
  return "Std_JSON_Utils_Views_Writers.Writer"
}
func (_this *CompanionStruct_Writer_) Witness() Writer__ {
  return Companion_Writer___.Create_Writer_(uint32(0), Companion_Chain_.Create_Empty_())
}
// End of class Writer

func Type_Writer_() _dafny.TypeDescriptor {
  return type_Writer_{}
}

type type_Writer_ struct {
}

func (_this type_Writer_) Default() interface{} {
  return Companion_Writer_.Witness()
}

func (_this type_Writer_) String() string {
  return "Std_JSON_Utils_Views_Writers.Writer"
}

// Definition of datatype Writer__
type Writer__ struct {
  Data_Writer___
}

func (_this Writer__) Get_() Data_Writer___ {
  return _this.Data_Writer___
}

type Data_Writer___ interface {
  isWriter__()
}

type CompanionStruct_Writer___ struct {
}
var Companion_Writer___ = CompanionStruct_Writer___ {
}

type Writer___Writer struct {
  Length uint32
  Chain Chain
}

func (Writer___Writer) isWriter__() {}

func (CompanionStruct_Writer___) Create_Writer_(Length uint32, Chain Chain) Writer__ {
  return Writer__{Writer___Writer{Length, Chain}}
}

func (_this Writer__) Is_Writer() bool {
  _, ok := _this.Get_().(Writer___Writer)
  return ok
}

func (CompanionStruct_Writer___) Default() Writer__ {
  return Companion_Writer___.Create_Writer_(uint32(0), Companion_Chain_.Default())
}

func (_this Writer__) Dtor_length() uint32 {
  return _this.Get_().(Writer___Writer).Length
}

func (_this Writer__) Dtor_chain() Chain {
  return _this.Get_().(Writer___Writer).Chain
}

func (_this Writer__) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case Writer___Writer: {
      return "Writers.Writer_.Writer" + "(" + _dafny.String(data.Length) + ", " + _dafny.String(data.Chain) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this Writer__) Equals(other Writer__) bool {
  switch data1 := _this.Get_().(type) {
    case Writer___Writer: {
      data2, ok := other.Get_().(Writer___Writer)
      return ok && data1.Length == data2.Length && data1.Chain.Equals(data2.Chain)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this Writer__) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(Writer__)
  return ok && _this.Equals(typed)
}

func Type_Writer___() _dafny.TypeDescriptor {
  return type_Writer___{}
}

type type_Writer___ struct {
}

func (_this type_Writer___) Default() interface{} {
  return Companion_Writer___.Default();
}

func (_this type_Writer___) String() string {
  return "Std_JSON_Utils_Views_Writers.Writer__"
}
func (_this Writer__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Writer__{}

func (_this Writer__) Bytes() _dafny.Sequence {
  {
    return ((_this).Dtor_chain()).Bytes()
  }
}
func (_static CompanionStruct_Writer___) SaturatedAddU32(a uint32, b uint32) uint32 {
  if ((a) <= ((Std_BoundedInts.Companion_Default___.UINT32__MAX()) - (func () uint32 { return  (b) })())) {
    return (a) + (b)
  } else {
    return Std_BoundedInts.Companion_Default___.UINT32__MAX()
  }
}
func (_this Writer__) Append(v_k Std_JSON_Utils_Views_Core.View__) Writer__ {
  {
    return Companion_Writer___.Create_Writer_(Companion_Writer___.SaturatedAddU32((_this).Dtor_length(), (v_k).Length()), ((_this).Dtor_chain()).Append(v_k))
  }
}
func (_this Writer__) Then(fn func (Writer__) Writer__) Writer__ {
  {
    return (fn)(_this)
  }
}
func (_this Writer__) CopyTo(dest _dafny.Array) {
  {
    ((_this).Dtor_chain()).CopyTo(dest, (_this).Dtor_length())
  }
}
func (_this Writer__) ToArray() _dafny.Array {
  {
    var bs _dafny.Array = _dafny.NewArrayWithValue(nil, _dafny.IntOf(0))
    _ = bs
    var _len0_4 _dafny.Int = _dafny.IntOfAny((_this).Dtor_length())
    _ = _len0_4
    var _nw5 _dafny.Array
    _ = _nw5
    if (_len0_4.Cmp(_dafny.Zero) == 0) {
      _nw5 = _dafny.NewArray(_len0_4)
    } else {
      var _init4 func (_dafny.Int) uint8 = func (_359_i _dafny.Int) uint8 {
        return uint8(0)
      }
      _ = _init4
      var _element0_4 = _init4(_dafny.Zero)
      _ = _element0_4
      _nw5 = _dafny.NewArrayFromExample(_element0_4, nil, _len0_4)
      (_nw5).ArraySet1Byte(_element0_4, 0)
      var _nativeLen0_4 = (_len0_4).Int()
      _ = _nativeLen0_4
      for _i0_4 := 1; _i0_4 < _nativeLen0_4; _i0_4++ {
        (_nw5).ArraySet1Byte(_init4(_dafny.IntOf(_i0_4)), _i0_4)
      }
    }
    bs = _nw5
    (_this).CopyTo(bs)
    return bs
  }
}
func (_static CompanionStruct_Writer___) Empty() Writer__ {
  return Companion_Writer___.Create_Writer_(uint32(0), Companion_Chain_.Create_Empty_())
}
func (_this Writer__) Unsaturated_q() bool {
  {
    return ((_this).Dtor_length()) != (Std_BoundedInts.Companion_Default___.UINT32__MAX())/* dircomp */
  }
}
func (_this Writer__) Empty_q() bool {
  {
    return ((_this).Dtor_chain()).Is_Empty()
  }
}
// End of datatype Writer__
