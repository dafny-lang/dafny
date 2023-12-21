// Package Std_JSON_Utils_Cursors
// Dafny module Std_JSON_Utils_Cursors compiled into Go

package Std_JSON_Utils_Cursors

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
  Std_JSON_Utils_Views_Writers "Std_JSON_Utils_Views_Writers"
  Std_JSON_Utils_Views "Std_JSON_Utils_Views"
  Std_JSON_Utils_Lexers_Core "Std_JSON_Utils_Lexers_Core"
  Std_JSON_Utils_Lexers_Strings "Std_JSON_Utils_Lexers_Strings"
  Std_JSON_Utils_Lexers "Std_JSON_Utils_Lexers"
)
var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Std_Wrappers.Dummy__
var _ Std_Concurrent.Dummy__
var _ Std_FileIOInternalExterns.Dummy__
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
var _ Std_JSON_Utils_Views_Writers.Dummy__
var _ Std_JSON_Utils_Views.Dummy__
var _ Std_JSON_Utils_Lexers_Core.Dummy__
var _ Std_JSON_Utils_Lexers_Strings.Dummy__
var _ Std_JSON_Utils_Lexers.Dummy__

type Dummy__ struct{}



// Definition of datatype Split
type Split struct {
  Data_Split_
}

func (_this Split) Get_() Data_Split_ {
  return _this.Data_Split_
}

type Data_Split_ interface {
  isSplit()
}

type CompanionStruct_Split_ struct {
}
var Companion_Split_ = CompanionStruct_Split_ {
}

type Split_SP struct {
  T interface{}
  Cs Cursor__
}

func (Split_SP) isSplit() {}

func (CompanionStruct_Split_) Create_SP_(T interface{}, Cs Cursor__) Split {
  return Split{Split_SP{T, Cs}}
}

func (_this Split) Is_SP() bool {
  _, ok := _this.Get_().(Split_SP)
  return ok
}

func (CompanionStruct_Split_) Default(_default_T interface{}) Split {
  return Companion_Split_.Create_SP_(_default_T, Companion_FreshCursor_.Witness())
}

func (_this Split) Dtor_t() interface{} {
  return _this.Get_().(Split_SP).T
}

func (_this Split) Dtor_cs() Cursor__ {
  return _this.Get_().(Split_SP).Cs
}

func (_this Split) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case Split_SP: {
      return "Cursors.Split.SP" + "(" + _dafny.String(data.T) + ", " + _dafny.String(data.Cs) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this Split) Equals(other Split) bool {
  switch data1 := _this.Get_().(type) {
    case Split_SP: {
      data2, ok := other.Get_().(Split_SP)
      return ok && _dafny.AreEqual(data1.T, data2.T) && data1.Cs.Equals(data2.Cs)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this Split) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(Split)
  return ok && _this.Equals(typed)
}

func Type_Split_(Type_T_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_Split_{Type_T_}
}

type type_Split_ struct {
  Type_T_ _dafny.TypeDescriptor
}

func (_this type_Split_) Default() interface{} {
  Type_T_ := _this.Type_T_
  _ = Type_T_
  return Companion_Split_.Default(Type_T_.Default());
}

func (_this type_Split_) String() string {
  return "Std_JSON_Utils_Cursors.Split"
}
func (_this Split) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Split{}

// End of datatype Split

// Definition of class Cursor
type Cursor struct {
}

func New_Cursor_() *Cursor {
  _this := Cursor{}

  return &_this
}

type CompanionStruct_Cursor_ struct {
}
var Companion_Cursor_ = CompanionStruct_Cursor_ {
}

func (*Cursor) String() string {
  return "Std_JSON_Utils_Cursors.Cursor"
}
func (_this *CompanionStruct_Cursor_) Witness() Cursor__ {
  return Companion_Cursor___.Create_Cursor_(_dafny.SeqOf(), uint32(0), uint32(0), uint32(0))
}
// End of class Cursor

func Type_Cursor_() _dafny.TypeDescriptor {
  return type_Cursor_{}
}

type type_Cursor_ struct {
}

func (_this type_Cursor_) Default() interface{} {
  return Companion_Cursor_.Witness()
}

func (_this type_Cursor_) String() string {
  return "Std_JSON_Utils_Cursors.Cursor"
}

// Definition of class FreshCursor
type FreshCursor struct {
}

func New_FreshCursor_() *FreshCursor {
  _this := FreshCursor{}

  return &_this
}

type CompanionStruct_FreshCursor_ struct {
}
var Companion_FreshCursor_ = CompanionStruct_FreshCursor_ {
}

func (*FreshCursor) String() string {
  return "Std_JSON_Utils_Cursors.FreshCursor"
}
func (_this *CompanionStruct_FreshCursor_) Witness() Cursor__ {
  return Companion_Cursor___.Create_Cursor_(_dafny.SeqOf(), uint32(0), uint32(0), uint32(0))
}
// End of class FreshCursor

func Type_FreshCursor_() _dafny.TypeDescriptor {
  return type_FreshCursor_{}
}

type type_FreshCursor_ struct {
}

func (_this type_FreshCursor_) Default() interface{} {
  return Companion_FreshCursor_.Witness()
}

func (_this type_FreshCursor_) String() string {
  return "Std_JSON_Utils_Cursors.FreshCursor"
}

// Definition of datatype CursorError
type CursorError struct {
  Data_CursorError_
}

func (_this CursorError) Get_() Data_CursorError_ {
  return _this.Data_CursorError_
}

type Data_CursorError_ interface {
  isCursorError()
}

type CompanionStruct_CursorError_ struct {
}
var Companion_CursorError_ = CompanionStruct_CursorError_ {
}

type CursorError_EOF struct {
}

func (CursorError_EOF) isCursorError() {}

func (CompanionStruct_CursorError_) Create_EOF_() CursorError {
  return CursorError{CursorError_EOF{}}
}

func (_this CursorError) Is_EOF() bool {
  _, ok := _this.Get_().(CursorError_EOF)
  return ok
}

type CursorError_ExpectingByte struct {
  Expected uint8
  B int16
}

func (CursorError_ExpectingByte) isCursorError() {}

func (CompanionStruct_CursorError_) Create_ExpectingByte_(Expected uint8, B int16) CursorError {
  return CursorError{CursorError_ExpectingByte{Expected, B}}
}

func (_this CursorError) Is_ExpectingByte() bool {
  _, ok := _this.Get_().(CursorError_ExpectingByte)
  return ok
}

type CursorError_ExpectingAnyByte struct {
  Expected__sq _dafny.Sequence
  B int16
}

func (CursorError_ExpectingAnyByte) isCursorError() {}

func (CompanionStruct_CursorError_) Create_ExpectingAnyByte_(Expected__sq _dafny.Sequence, B int16) CursorError {
  return CursorError{CursorError_ExpectingAnyByte{Expected__sq, B}}
}

func (_this CursorError) Is_ExpectingAnyByte() bool {
  _, ok := _this.Get_().(CursorError_ExpectingAnyByte)
  return ok
}

type CursorError_OtherError struct {
  Err interface{}
}

func (CursorError_OtherError) isCursorError() {}

func (CompanionStruct_CursorError_) Create_OtherError_(Err interface{}) CursorError {
  return CursorError{CursorError_OtherError{Err}}
}

func (_this CursorError) Is_OtherError() bool {
  _, ok := _this.Get_().(CursorError_OtherError)
  return ok
}

func (CompanionStruct_CursorError_) Default() CursorError {
  return Companion_CursorError_.Create_EOF_()
}

func (_this CursorError) Dtor_expected() uint8 {
  return _this.Get_().(CursorError_ExpectingByte).Expected
}

func (_this CursorError) Dtor_b() int16 {
  switch data := _this.Get_().(type) {
    case CursorError_ExpectingByte: return data.B
    default: return data.(CursorError_ExpectingAnyByte).B
  }
}

func (_this CursorError) Dtor_expected__sq() _dafny.Sequence {
  return _this.Get_().(CursorError_ExpectingAnyByte).Expected__sq
}

func (_this CursorError) Dtor_err() interface{} {
  return _this.Get_().(CursorError_OtherError).Err
}

func (_this CursorError) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case CursorError_EOF: {
      return "Cursors.CursorError.EOF"
    }
    case CursorError_ExpectingByte: {
      return "Cursors.CursorError.ExpectingByte" + "(" + _dafny.String(data.Expected) + ", " + _dafny.String(data.B) + ")"
    }
    case CursorError_ExpectingAnyByte: {
      return "Cursors.CursorError.ExpectingAnyByte" + "(" + _dafny.String(data.Expected__sq) + ", " + _dafny.String(data.B) + ")"
    }
    case CursorError_OtherError: {
      return "Cursors.CursorError.OtherError" + "(" + _dafny.String(data.Err) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this CursorError) Equals(other CursorError) bool {
  switch data1 := _this.Get_().(type) {
    case CursorError_EOF: {
      _, ok := other.Get_().(CursorError_EOF)
      return ok
    }
    case CursorError_ExpectingByte: {
      data2, ok := other.Get_().(CursorError_ExpectingByte)
      return ok && data1.Expected == data2.Expected && data1.B == data2.B
    }
    case CursorError_ExpectingAnyByte: {
      data2, ok := other.Get_().(CursorError_ExpectingAnyByte)
      return ok && data1.Expected__sq.Equals(data2.Expected__sq) && data1.B == data2.B
    }
    case CursorError_OtherError: {
      data2, ok := other.Get_().(CursorError_OtherError)
      return ok && _dafny.AreEqual(data1.Err, data2.Err)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this CursorError) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(CursorError)
  return ok && _this.Equals(typed)
}

func Type_CursorError_() _dafny.TypeDescriptor {
  return type_CursorError_{}
}

type type_CursorError_ struct {
}

func (_this type_CursorError_) Default() interface{} {
  return Companion_CursorError_.Default();
}

func (_this type_CursorError_) String() string {
  return "Std_JSON_Utils_Cursors.CursorError"
}
func (_this CursorError) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = CursorError{}

func (_this CursorError) ToString(pr func (interface{}) _dafny.Sequence) _dafny.Sequence {
  {
    var _source14 CursorError = _this
    _ = _source14
    if (_source14.Is_EOF()) {
      return _dafny.UnicodeSeqOfUtf8Bytes("Reached EOF")
    } else if (_source14.Is_ExpectingByte()) {
      var _362___mcc_h0 uint8 = _source14.Get_().(CursorError_ExpectingByte).Expected
      _ = _362___mcc_h0
      var _363___mcc_h1 int16 = _source14.Get_().(CursorError_ExpectingByte).B
      _ = _363___mcc_h1
      var _364_b int16 = _363___mcc_h1
      _ = _364_b
      var _365_b0 uint8 = _362___mcc_h0
      _ = _365_b0
      var _366_c _dafny.Sequence = (func () _dafny.Sequence { if (_364_b) > (int16(0)) { return _dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(_dafny.UnicodeSeqOfUtf8Bytes("'"), _dafny.SeqOf(_dafny.CodePoint((_364_b)))), _dafny.UnicodeSeqOfUtf8Bytes("'")) }; return _dafny.UnicodeSeqOfUtf8Bytes("EOF") })() 
      _ = _366_c
      return _dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(_dafny.UnicodeSeqOfUtf8Bytes("Expecting '"), _dafny.SeqOf(_dafny.CodePoint((_365_b0)))), _dafny.UnicodeSeqOfUtf8Bytes("', read ")), _366_c)
    } else if (_source14.Is_ExpectingAnyByte()) {
      var _367___mcc_h2 _dafny.Sequence = _source14.Get_().(CursorError_ExpectingAnyByte).Expected__sq
      _ = _367___mcc_h2
      var _368___mcc_h3 int16 = _source14.Get_().(CursorError_ExpectingAnyByte).B
      _ = _368___mcc_h3
      var _369_b int16 = _368___mcc_h3
      _ = _369_b
      var _370_bs0 _dafny.Sequence = _367___mcc_h2
      _ = _370_bs0
      var _371_c _dafny.Sequence = (func () _dafny.Sequence { if (_369_b) > (int16(0)) { return _dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(_dafny.UnicodeSeqOfUtf8Bytes("'"), _dafny.SeqOf(_dafny.CodePoint((_369_b)))), _dafny.UnicodeSeqOfUtf8Bytes("'")) }; return _dafny.UnicodeSeqOfUtf8Bytes("EOF") })() 
      _ = _371_c
      var _372_c0s _dafny.Sequence = _dafny.SeqCreate((_dafny.IntOfUint32((_370_bs0).Cardinality())).Uint32(), func (coer29 func (_dafny.Int) _dafny.CodePoint) func (_dafny.Int) interface{} {
        return func (arg31 _dafny.Int) interface{} {
          return coer29(arg31)
        }
      }((func (_373_bs0 _dafny.Sequence) func (_dafny.Int) _dafny.CodePoint {
        return func (_374_idx _dafny.Int) _dafny.CodePoint {
          return _dafny.CodePoint(((_373_bs0).Select((_374_idx).Uint32()).(uint8)))
        }
      })(_370_bs0)))
      _ = _372_c0s
      return _dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(_dafny.UnicodeSeqOfUtf8Bytes("Expecting one of '"), _372_c0s), _dafny.UnicodeSeqOfUtf8Bytes("', read ")), _371_c)
    } else {
      var _375___mcc_h4 interface{} = _source14.Get_().(CursorError_OtherError).Err
      _ = _375___mcc_h4
      var _376_err interface{} = _375___mcc_h4
      _ = _376_err
      return (pr)(_376_err)
    }
  }
}
// End of datatype CursorError

// Definition of datatype Cursor__
type Cursor__ struct {
  Data_Cursor___
}

func (_this Cursor__) Get_() Data_Cursor___ {
  return _this.Data_Cursor___
}

type Data_Cursor___ interface {
  isCursor__()
}

type CompanionStruct_Cursor___ struct {
}
var Companion_Cursor___ = CompanionStruct_Cursor___ {
}

type Cursor___Cursor struct {
  S _dafny.Sequence
  Beg uint32
  Point uint32
  End uint32
}

func (Cursor___Cursor) isCursor__() {}

func (CompanionStruct_Cursor___) Create_Cursor_(S _dafny.Sequence, Beg uint32, Point uint32, End uint32) Cursor__ {
  return Cursor__{Cursor___Cursor{S, Beg, Point, End}}
}

func (_this Cursor__) Is_Cursor() bool {
  _, ok := _this.Get_().(Cursor___Cursor)
  return ok
}

func (CompanionStruct_Cursor___) Default() Cursor__ {
  return Companion_Cursor___.Create_Cursor_(_dafny.EmptySeq, uint32(0), uint32(0), uint32(0))
}

func (_this Cursor__) Dtor_s() _dafny.Sequence {
  return _this.Get_().(Cursor___Cursor).S
}

func (_this Cursor__) Dtor_beg() uint32 {
  return _this.Get_().(Cursor___Cursor).Beg
}

func (_this Cursor__) Dtor_point() uint32 {
  return _this.Get_().(Cursor___Cursor).Point
}

func (_this Cursor__) Dtor_end() uint32 {
  return _this.Get_().(Cursor___Cursor).End
}

func (_this Cursor__) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case Cursor___Cursor: {
      return "Cursors.Cursor_.Cursor" + "(" + _dafny.String(data.S) + ", " + _dafny.String(data.Beg) + ", " + _dafny.String(data.Point) + ", " + _dafny.String(data.End) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this Cursor__) Equals(other Cursor__) bool {
  switch data1 := _this.Get_().(type) {
    case Cursor___Cursor: {
      data2, ok := other.Get_().(Cursor___Cursor)
      return ok && data1.S.Equals(data2.S) && data1.Beg == data2.Beg && data1.Point == data2.Point && data1.End == data2.End
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this Cursor__) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(Cursor__)
  return ok && _this.Equals(typed)
}

func Type_Cursor___() _dafny.TypeDescriptor {
  return type_Cursor___{}
}

type type_Cursor___ struct {
}

func (_this type_Cursor___) Default() interface{} {
  return Companion_Cursor___.Default();
}

func (_this type_Cursor___) String() string {
  return "Std_JSON_Utils_Cursors.Cursor__"
}
func (_this Cursor__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Cursor__{}

func (_static CompanionStruct_Cursor___) OfView(v Std_JSON_Utils_Views_Core.View__) Cursor__ {
  return Companion_Cursor___.Create_Cursor_((v).Dtor_s(), (v).Dtor_beg(), (v).Dtor_beg(), (v).Dtor_end())
}
func (_static CompanionStruct_Cursor___) OfBytes(bs _dafny.Sequence) Cursor__ {
  return Companion_Cursor___.Create_Cursor_(bs, uint32(0), uint32(0), uint32((bs).Cardinality()))
}
func (_this Cursor__) Bytes() _dafny.Sequence {
  {
    return ((_this).Dtor_s()).Subsequence(uint32((_this).Dtor_beg()), uint32((_this).Dtor_end()))
  }
}
func (_this Cursor__) Prefix() Std_JSON_Utils_Views_Core.View__ {
  {
    return Std_JSON_Utils_Views_Core.Companion_View___.Create_View_((_this).Dtor_s(), (_this).Dtor_beg(), (_this).Dtor_point())
  }
}
func (_this Cursor__) Suffix() Cursor__ {
  {
    var _377_dt__update__tmp_h0 Cursor__ = _this
    _ = _377_dt__update__tmp_h0
    var _378_dt__update_hbeg_h0 uint32 = (_this).Dtor_point()
    _ = _378_dt__update_hbeg_h0
    return Companion_Cursor___.Create_Cursor_((_377_dt__update__tmp_h0).Dtor_s(), _378_dt__update_hbeg_h0, (_377_dt__update__tmp_h0).Dtor_point(), (_377_dt__update__tmp_h0).Dtor_end())
  }
}
func (_this Cursor__) Split() Split {
  {
    return Companion_Split_.Create_SP_((_this).Prefix(), (_this).Suffix())
  }
}
func (_this Cursor__) PrefixLength() uint32 {
  {
    return ((_this).Dtor_point()) - (func () uint32 { return  ((_this).Dtor_beg()) })()
  }
}
func (_this Cursor__) SuffixLength() uint32 {
  {
    return ((_this).Dtor_end()) - (func () uint32 { return  ((_this).Dtor_point()) })()
  }
}
func (_this Cursor__) Length() uint32 {
  {
    return ((_this).Dtor_end()) - (func () uint32 { return  ((_this).Dtor_beg()) })()
  }
}
func (_this Cursor__) At(idx uint32) uint8 {
  {
    return ((_this).Dtor_s()).Select(uint32(((_this).Dtor_beg()) + (idx))).(uint8)
  }
}
func (_this Cursor__) SuffixAt(idx uint32) uint8 {
  {
    return ((_this).Dtor_s()).Select(uint32(((_this).Dtor_point()) + (idx))).(uint8)
  }
}
func (_this Cursor__) Peek() int16 {
  {
    if ((_this).EOF_q()) {
      return int16(-1)
    } else {
      return int16((_this).SuffixAt(uint32(0)))
    }
  }
}
func (_this Cursor__) LookingAt(c _dafny.CodePoint) bool {
  {
    return ((_this).Peek()) == (int16(c))
  }
}
func (_this Cursor__) Skip(n uint32) Cursor__ {
  {
    var _379_dt__update__tmp_h0 Cursor__ = _this
    _ = _379_dt__update__tmp_h0
    var _380_dt__update_hpoint_h0 uint32 = ((_this).Dtor_point()) + (n)
    _ = _380_dt__update_hpoint_h0
    return Companion_Cursor___.Create_Cursor_((_379_dt__update__tmp_h0).Dtor_s(), (_379_dt__update__tmp_h0).Dtor_beg(), _380_dt__update_hpoint_h0, (_379_dt__update__tmp_h0).Dtor_end())
  }
}
func (_this Cursor__) Unskip(n uint32) Cursor__ {
  {
    var _381_dt__update__tmp_h0 Cursor__ = _this
    _ = _381_dt__update__tmp_h0
    var _382_dt__update_hpoint_h0 uint32 = ((_this).Dtor_point()) - (func () uint32 { return  (n) })()
    _ = _382_dt__update_hpoint_h0
    return Companion_Cursor___.Create_Cursor_((_381_dt__update__tmp_h0).Dtor_s(), (_381_dt__update__tmp_h0).Dtor_beg(), _382_dt__update_hpoint_h0, (_381_dt__update__tmp_h0).Dtor_end())
  }
}
func (_this Cursor__) Get(err interface{}) Std_Wrappers.Result {
  {
    if ((_this).EOF_q()) {
      return Std_Wrappers.Companion_Result_.Create_Failure_(Companion_CursorError_.Create_OtherError_(err))
    } else {
      return Std_Wrappers.Companion_Result_.Create_Success_((_this).Skip(uint32(1)))
    }
  }
}
func (_this Cursor__) AssertByte(b uint8) Std_Wrappers.Result {
  {
    var _383_nxt int16 = (_this).Peek()
    _ = _383_nxt
    if ((_383_nxt) == (int16(b))) {
      return Std_Wrappers.Companion_Result_.Create_Success_((_this).Skip(uint32(1)))
    } else {
      return Std_Wrappers.Companion_Result_.Create_Failure_(Companion_CursorError_.Create_ExpectingByte_(b, _383_nxt))
    }
  }
}
func (_this Cursor__) AssertBytes(bs _dafny.Sequence, offset uint32) Std_Wrappers.Result {
  {
    goto TAIL_CALL_START
    TAIL_CALL_START:
    if ((offset) == (uint32((bs).Cardinality()))) {
      return Std_Wrappers.Companion_Result_.Create_Success_(_this)
    } else {
      var _384_valueOrError0 Std_Wrappers.Result = (_this).AssertByte(((bs).Select(uint32(offset)).(uint8)))
      _ = _384_valueOrError0
      if ((_384_valueOrError0).IsFailure()) {
        return (_384_valueOrError0).PropagateFailure()
      } else {
        var _385_ps Cursor__ = (_384_valueOrError0).Extract().(Cursor__)
        _ = _385_ps
        var _in70 Cursor__ = _385_ps
        _ = _in70
        var _in71 _dafny.Sequence = bs
        _ = _in71
        var _in72 uint32 = (offset) + (uint32(1))
        _ = _in72
        _this = _in70
        
        bs = _in71
        offset = _in72
        goto TAIL_CALL_START
      }
    }
  }
}
func (_this Cursor__) AssertChar(c0 _dafny.CodePoint) Std_Wrappers.Result {
  {
    return (_this).AssertByte(uint8(c0))
  }
}
func (_this Cursor__) SkipByte() Cursor__ {
  {
    if ((_this).EOF_q()) {
      return _this
    } else {
      return (_this).Skip(uint32(1))
    }
  }
}
func (_this Cursor__) SkipIf(p func (uint8) bool) Cursor__ {
  {
    if (((_this).EOF_q()) || (!((p)((_this).SuffixAt(uint32(0)))))) {
      return _this
    } else {
      return (_this).Skip(uint32(1))
    }
  }
}
func (_this Cursor__) SkipWhile(p func (uint8) bool) Cursor__ {
  {
    var ps Cursor__ = Companion_Cursor_.Witness()
    _ = ps
    var _386_point_k uint32
    _ = _386_point_k
    _386_point_k = (_this).Dtor_point()
    var _387_end uint32
    _ = _387_end
    _387_end = (_this).Dtor_end()
    for ((_386_point_k) < (_387_end)) && ((p)(((_this).Dtor_s()).Select(uint32(_386_point_k)).(uint8))) {
      _386_point_k = (_386_point_k) + (uint32(1))
    }
    ps = Companion_Cursor___.Create_Cursor_((_this).Dtor_s(), (_this).Dtor_beg(), _386_point_k, (_this).Dtor_end())
    return ps
    return ps
  }
}
func (_this Cursor__) SkipWhileLexer(step func (interface{}, int16) Std_JSON_Utils_Lexers_Core.LexerResult, st interface{}) Std_Wrappers.Result {
  {
    var pr Std_Wrappers.Result = Std_Wrappers.Companion_Result_.Default(Companion_Cursor_.Witness())
    _ = pr
    var _388_point_k uint32
    _ = _388_point_k
    _388_point_k = (_this).Dtor_point()
    var _389_end uint32
    _ = _389_end
    _389_end = (_this).Dtor_end()
    var _390_st_k interface{}
    _ = _390_st_k
    _390_st_k = st
    for true {
      var _391_eof bool
      _ = _391_eof
      _391_eof = (_388_point_k) == (_389_end)
      var _392_minusone int16
      _ = _392_minusone
      _392_minusone = int16(-1)
      var _393_c int16
      _ = _393_c
      _393_c = (func () int16 { if _391_eof { return _392_minusone }; return int16(((_this).Dtor_s()).Select(uint32(_388_point_k)).(uint8)) })() 
      var _source15 Std_JSON_Utils_Lexers_Core.LexerResult = (step)(_390_st_k, _393_c)
      _ = _source15
      if (_source15.Is_Accept()) {
        pr = Std_Wrappers.Companion_Result_.Create_Success_(Companion_Cursor___.Create_Cursor_((_this).Dtor_s(), (_this).Dtor_beg(), _388_point_k, (_this).Dtor_end()))
        return pr
      } else if (_source15.Is_Reject()) {
        var _394___mcc_h0 interface{} = _source15.Get_().(Std_JSON_Utils_Lexers_Core.LexerResult_Reject).Err
        _ = _394___mcc_h0
        var _395_err interface{} = _394___mcc_h0
        _ = _395_err
        pr = Std_Wrappers.Companion_Result_.Create_Failure_(Companion_CursorError_.Create_OtherError_(_395_err))
        return pr
      } else {
        var _396___mcc_h1 interface{} = _source15.Get_().(Std_JSON_Utils_Lexers_Core.LexerResult_Partial).St
        _ = _396___mcc_h1
        var _397_st_k_k interface{} = _396___mcc_h1
        _ = _397_st_k_k
        if (_391_eof) {
          pr = Std_Wrappers.Companion_Result_.Create_Failure_(Companion_CursorError_.Create_EOF_())
          return pr
        } else {
          _390_st_k = _397_st_k_k
          _388_point_k = (_388_point_k) + (uint32(1))
        }
      }
    }
    return pr
  }
}
func (_this Cursor__) BOF_q() bool {
  {
    return ((_this).Dtor_point()) == ((_this).Dtor_beg())
  }
}
func (_this Cursor__) EOF_q() bool {
  {
    return ((_this).Dtor_point()) == ((_this).Dtor_end())
  }
}
// End of datatype Cursor__
