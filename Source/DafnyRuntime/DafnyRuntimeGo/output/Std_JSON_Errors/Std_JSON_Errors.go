// Package Std_JSON_Errors
// Dafny module Std_JSON_Errors compiled into Go

package Std_JSON_Errors

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

type Dummy__ struct{}



// Definition of datatype DeserializationError
type DeserializationError struct {
  Data_DeserializationError_
}

func (_this DeserializationError) Get_() Data_DeserializationError_ {
  return _this.Data_DeserializationError_
}

type Data_DeserializationError_ interface {
  isDeserializationError()
}

type CompanionStruct_DeserializationError_ struct {
}
var Companion_DeserializationError_ = CompanionStruct_DeserializationError_ {
}

type DeserializationError_UnterminatedSequence struct {
}

func (DeserializationError_UnterminatedSequence) isDeserializationError() {}

func (CompanionStruct_DeserializationError_) Create_UnterminatedSequence_() DeserializationError {
  return DeserializationError{DeserializationError_UnterminatedSequence{}}
}

func (_this DeserializationError) Is_UnterminatedSequence() bool {
  _, ok := _this.Get_().(DeserializationError_UnterminatedSequence)
  return ok
}

type DeserializationError_UnsupportedEscape struct {
  Str _dafny.Sequence
}

func (DeserializationError_UnsupportedEscape) isDeserializationError() {}

func (CompanionStruct_DeserializationError_) Create_UnsupportedEscape_(Str _dafny.Sequence) DeserializationError {
  return DeserializationError{DeserializationError_UnsupportedEscape{Str}}
}

func (_this DeserializationError) Is_UnsupportedEscape() bool {
  _, ok := _this.Get_().(DeserializationError_UnsupportedEscape)
  return ok
}

type DeserializationError_EscapeAtEOS struct {
}

func (DeserializationError_EscapeAtEOS) isDeserializationError() {}

func (CompanionStruct_DeserializationError_) Create_EscapeAtEOS_() DeserializationError {
  return DeserializationError{DeserializationError_EscapeAtEOS{}}
}

func (_this DeserializationError) Is_EscapeAtEOS() bool {
  _, ok := _this.Get_().(DeserializationError_EscapeAtEOS)
  return ok
}

type DeserializationError_EmptyNumber struct {
}

func (DeserializationError_EmptyNumber) isDeserializationError() {}

func (CompanionStruct_DeserializationError_) Create_EmptyNumber_() DeserializationError {
  return DeserializationError{DeserializationError_EmptyNumber{}}
}

func (_this DeserializationError) Is_EmptyNumber() bool {
  _, ok := _this.Get_().(DeserializationError_EmptyNumber)
  return ok
}

type DeserializationError_ExpectingEOF struct {
}

func (DeserializationError_ExpectingEOF) isDeserializationError() {}

func (CompanionStruct_DeserializationError_) Create_ExpectingEOF_() DeserializationError {
  return DeserializationError{DeserializationError_ExpectingEOF{}}
}

func (_this DeserializationError) Is_ExpectingEOF() bool {
  _, ok := _this.Get_().(DeserializationError_ExpectingEOF)
  return ok
}

type DeserializationError_IntOverflow struct {
}

func (DeserializationError_IntOverflow) isDeserializationError() {}

func (CompanionStruct_DeserializationError_) Create_IntOverflow_() DeserializationError {
  return DeserializationError{DeserializationError_IntOverflow{}}
}

func (_this DeserializationError) Is_IntOverflow() bool {
  _, ok := _this.Get_().(DeserializationError_IntOverflow)
  return ok
}

type DeserializationError_ReachedEOF struct {
}

func (DeserializationError_ReachedEOF) isDeserializationError() {}

func (CompanionStruct_DeserializationError_) Create_ReachedEOF_() DeserializationError {
  return DeserializationError{DeserializationError_ReachedEOF{}}
}

func (_this DeserializationError) Is_ReachedEOF() bool {
  _, ok := _this.Get_().(DeserializationError_ReachedEOF)
  return ok
}

type DeserializationError_ExpectingByte struct {
  Expected uint8
  B int16
}

func (DeserializationError_ExpectingByte) isDeserializationError() {}

func (CompanionStruct_DeserializationError_) Create_ExpectingByte_(Expected uint8, B int16) DeserializationError {
  return DeserializationError{DeserializationError_ExpectingByte{Expected, B}}
}

func (_this DeserializationError) Is_ExpectingByte() bool {
  _, ok := _this.Get_().(DeserializationError_ExpectingByte)
  return ok
}

type DeserializationError_ExpectingAnyByte struct {
  Expected__sq _dafny.Sequence
  B int16
}

func (DeserializationError_ExpectingAnyByte) isDeserializationError() {}

func (CompanionStruct_DeserializationError_) Create_ExpectingAnyByte_(Expected__sq _dafny.Sequence, B int16) DeserializationError {
  return DeserializationError{DeserializationError_ExpectingAnyByte{Expected__sq, B}}
}

func (_this DeserializationError) Is_ExpectingAnyByte() bool {
  _, ok := _this.Get_().(DeserializationError_ExpectingAnyByte)
  return ok
}

type DeserializationError_InvalidUnicode struct {
}

func (DeserializationError_InvalidUnicode) isDeserializationError() {}

func (CompanionStruct_DeserializationError_) Create_InvalidUnicode_() DeserializationError {
  return DeserializationError{DeserializationError_InvalidUnicode{}}
}

func (_this DeserializationError) Is_InvalidUnicode() bool {
  _, ok := _this.Get_().(DeserializationError_InvalidUnicode)
  return ok
}

func (CompanionStruct_DeserializationError_) Default() DeserializationError {
  return Companion_DeserializationError_.Create_UnterminatedSequence_()
}

func (_this DeserializationError) Dtor_str() _dafny.Sequence {
  return _this.Get_().(DeserializationError_UnsupportedEscape).Str
}

func (_this DeserializationError) Dtor_expected() uint8 {
  return _this.Get_().(DeserializationError_ExpectingByte).Expected
}

func (_this DeserializationError) Dtor_b() int16 {
  switch data := _this.Get_().(type) {
    case DeserializationError_ExpectingByte: return data.B
    default: return data.(DeserializationError_ExpectingAnyByte).B
  }
}

func (_this DeserializationError) Dtor_expected__sq() _dafny.Sequence {
  return _this.Get_().(DeserializationError_ExpectingAnyByte).Expected__sq
}

func (_this DeserializationError) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case DeserializationError_UnterminatedSequence: {
      return "Errors.DeserializationError.UnterminatedSequence"
    }
    case DeserializationError_UnsupportedEscape: {
      return "Errors.DeserializationError.UnsupportedEscape" + "(" + data.Str.VerbatimString(true) + ")"
    }
    case DeserializationError_EscapeAtEOS: {
      return "Errors.DeserializationError.EscapeAtEOS"
    }
    case DeserializationError_EmptyNumber: {
      return "Errors.DeserializationError.EmptyNumber"
    }
    case DeserializationError_ExpectingEOF: {
      return "Errors.DeserializationError.ExpectingEOF"
    }
    case DeserializationError_IntOverflow: {
      return "Errors.DeserializationError.IntOverflow"
    }
    case DeserializationError_ReachedEOF: {
      return "Errors.DeserializationError.ReachedEOF"
    }
    case DeserializationError_ExpectingByte: {
      return "Errors.DeserializationError.ExpectingByte" + "(" + _dafny.String(data.Expected) + ", " + _dafny.String(data.B) + ")"
    }
    case DeserializationError_ExpectingAnyByte: {
      return "Errors.DeserializationError.ExpectingAnyByte" + "(" + _dafny.String(data.Expected__sq) + ", " + _dafny.String(data.B) + ")"
    }
    case DeserializationError_InvalidUnicode: {
      return "Errors.DeserializationError.InvalidUnicode"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this DeserializationError) Equals(other DeserializationError) bool {
  switch data1 := _this.Get_().(type) {
    case DeserializationError_UnterminatedSequence: {
      _, ok := other.Get_().(DeserializationError_UnterminatedSequence)
      return ok
    }
    case DeserializationError_UnsupportedEscape: {
      data2, ok := other.Get_().(DeserializationError_UnsupportedEscape)
      return ok && data1.Str.Equals(data2.Str)
    }
    case DeserializationError_EscapeAtEOS: {
      _, ok := other.Get_().(DeserializationError_EscapeAtEOS)
      return ok
    }
    case DeserializationError_EmptyNumber: {
      _, ok := other.Get_().(DeserializationError_EmptyNumber)
      return ok
    }
    case DeserializationError_ExpectingEOF: {
      _, ok := other.Get_().(DeserializationError_ExpectingEOF)
      return ok
    }
    case DeserializationError_IntOverflow: {
      _, ok := other.Get_().(DeserializationError_IntOverflow)
      return ok
    }
    case DeserializationError_ReachedEOF: {
      _, ok := other.Get_().(DeserializationError_ReachedEOF)
      return ok
    }
    case DeserializationError_ExpectingByte: {
      data2, ok := other.Get_().(DeserializationError_ExpectingByte)
      return ok && data1.Expected == data2.Expected && data1.B == data2.B
    }
    case DeserializationError_ExpectingAnyByte: {
      data2, ok := other.Get_().(DeserializationError_ExpectingAnyByte)
      return ok && data1.Expected__sq.Equals(data2.Expected__sq) && data1.B == data2.B
    }
    case DeserializationError_InvalidUnicode: {
      _, ok := other.Get_().(DeserializationError_InvalidUnicode)
      return ok
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this DeserializationError) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(DeserializationError)
  return ok && _this.Equals(typed)
}

func Type_DeserializationError_() _dafny.TypeDescriptor {
  return type_DeserializationError_{}
}

type type_DeserializationError_ struct {
}

func (_this type_DeserializationError_) Default() interface{} {
  return Companion_DeserializationError_.Default();
}

func (_this type_DeserializationError_) String() string {
  return "Std_JSON_Errors.DeserializationError"
}
func (_this DeserializationError) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = DeserializationError{}

func (_this DeserializationError) ToString() _dafny.Sequence {
  {
    var _source10 DeserializationError = _this
    _ = _source10
    if (_source10.Is_UnterminatedSequence()) {
      return _dafny.UnicodeSeqOfUtf8Bytes("Unterminated sequence")
    } else if (_source10.Is_UnsupportedEscape()) {
      var _292___mcc_h0 _dafny.Sequence = _source10.Get_().(DeserializationError_UnsupportedEscape).Str
      _ = _292___mcc_h0
      var _293_str _dafny.Sequence = _292___mcc_h0
      _ = _293_str
      return _dafny.Companion_Sequence_.Concatenate(_dafny.UnicodeSeqOfUtf8Bytes("Unsupported escape sequence: "), _293_str)
    } else if (_source10.Is_EscapeAtEOS()) {
      return _dafny.UnicodeSeqOfUtf8Bytes("Escape character at end of string")
    } else if (_source10.Is_EmptyNumber()) {
      return _dafny.UnicodeSeqOfUtf8Bytes("Number must contain at least one digit")
    } else if (_source10.Is_ExpectingEOF()) {
      return _dafny.UnicodeSeqOfUtf8Bytes("Expecting EOF")
    } else if (_source10.Is_IntOverflow()) {
      return _dafny.UnicodeSeqOfUtf8Bytes("Input length does not fit in a 32-bit counter")
    } else if (_source10.Is_ReachedEOF()) {
      return _dafny.UnicodeSeqOfUtf8Bytes("Reached EOF")
    } else if (_source10.Is_ExpectingByte()) {
      var _294___mcc_h1 uint8 = _source10.Get_().(DeserializationError_ExpectingByte).Expected
      _ = _294___mcc_h1
      var _295___mcc_h2 int16 = _source10.Get_().(DeserializationError_ExpectingByte).B
      _ = _295___mcc_h2
      var _296_b int16 = _295___mcc_h2
      _ = _296_b
      var _297_b0 uint8 = _294___mcc_h1
      _ = _297_b0
      var _298_c _dafny.Sequence = (func () _dafny.Sequence { if (_296_b) > (int16(0)) { return _dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(_dafny.UnicodeSeqOfUtf8Bytes("'"), _dafny.SeqOf(_dafny.CodePoint((_296_b)))), _dafny.UnicodeSeqOfUtf8Bytes("'")) }; return _dafny.UnicodeSeqOfUtf8Bytes("EOF") })() 
      _ = _298_c
      return _dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(_dafny.UnicodeSeqOfUtf8Bytes("Expecting '"), _dafny.SeqOf(_dafny.CodePoint((_297_b0)))), _dafny.UnicodeSeqOfUtf8Bytes("', read ")), _298_c)
    } else if (_source10.Is_ExpectingAnyByte()) {
      var _299___mcc_h3 _dafny.Sequence = _source10.Get_().(DeserializationError_ExpectingAnyByte).Expected__sq
      _ = _299___mcc_h3
      var _300___mcc_h4 int16 = _source10.Get_().(DeserializationError_ExpectingAnyByte).B
      _ = _300___mcc_h4
      var _301_b int16 = _300___mcc_h4
      _ = _301_b
      var _302_bs0 _dafny.Sequence = _299___mcc_h3
      _ = _302_bs0
      var _303_c _dafny.Sequence = (func () _dafny.Sequence { if (_301_b) > (int16(0)) { return _dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(_dafny.UnicodeSeqOfUtf8Bytes("'"), _dafny.SeqOf(_dafny.CodePoint((_301_b)))), _dafny.UnicodeSeqOfUtf8Bytes("'")) }; return _dafny.UnicodeSeqOfUtf8Bytes("EOF") })() 
      _ = _303_c
      var _304_c0s _dafny.Sequence = _dafny.SeqCreate((_dafny.IntOfUint32((_302_bs0).Cardinality())).Uint32(), func (coer24 func (_dafny.Int) _dafny.CodePoint) func (_dafny.Int) interface{} {
        return func (arg26 _dafny.Int) interface{} {
          return coer24(arg26)
        }
      }((func (_305_bs0 _dafny.Sequence) func (_dafny.Int) _dafny.CodePoint {
        return func (_306_idx _dafny.Int) _dafny.CodePoint {
          return _dafny.CodePoint(((_305_bs0).Select((_306_idx).Uint32()).(uint8)))
        }
      })(_302_bs0)))
      _ = _304_c0s
      return _dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(_dafny.UnicodeSeqOfUtf8Bytes("Expecting one of '"), _304_c0s), _dafny.UnicodeSeqOfUtf8Bytes("', read ")), _303_c)
    } else {
      return _dafny.UnicodeSeqOfUtf8Bytes("Invalid Unicode sequence")
    }
  }
}
// End of datatype DeserializationError

// Definition of datatype SerializationError
type SerializationError struct {
  Data_SerializationError_
}

func (_this SerializationError) Get_() Data_SerializationError_ {
  return _this.Data_SerializationError_
}

type Data_SerializationError_ interface {
  isSerializationError()
}

type CompanionStruct_SerializationError_ struct {
}
var Companion_SerializationError_ = CompanionStruct_SerializationError_ {
}

type SerializationError_OutOfMemory struct {
}

func (SerializationError_OutOfMemory) isSerializationError() {}

func (CompanionStruct_SerializationError_) Create_OutOfMemory_() SerializationError {
  return SerializationError{SerializationError_OutOfMemory{}}
}

func (_this SerializationError) Is_OutOfMemory() bool {
  _, ok := _this.Get_().(SerializationError_OutOfMemory)
  return ok
}

type SerializationError_IntTooLarge struct {
  I _dafny.Int
}

func (SerializationError_IntTooLarge) isSerializationError() {}

func (CompanionStruct_SerializationError_) Create_IntTooLarge_(I _dafny.Int) SerializationError {
  return SerializationError{SerializationError_IntTooLarge{I}}
}

func (_this SerializationError) Is_IntTooLarge() bool {
  _, ok := _this.Get_().(SerializationError_IntTooLarge)
  return ok
}

type SerializationError_StringTooLong struct {
  S _dafny.Sequence
}

func (SerializationError_StringTooLong) isSerializationError() {}

func (CompanionStruct_SerializationError_) Create_StringTooLong_(S _dafny.Sequence) SerializationError {
  return SerializationError{SerializationError_StringTooLong{S}}
}

func (_this SerializationError) Is_StringTooLong() bool {
  _, ok := _this.Get_().(SerializationError_StringTooLong)
  return ok
}

type SerializationError_InvalidUnicode struct {
}

func (SerializationError_InvalidUnicode) isSerializationError() {}

func (CompanionStruct_SerializationError_) Create_InvalidUnicode_() SerializationError {
  return SerializationError{SerializationError_InvalidUnicode{}}
}

func (_this SerializationError) Is_InvalidUnicode() bool {
  _, ok := _this.Get_().(SerializationError_InvalidUnicode)
  return ok
}

func (CompanionStruct_SerializationError_) Default() SerializationError {
  return Companion_SerializationError_.Create_OutOfMemory_()
}

func (_this SerializationError) Dtor_i() _dafny.Int {
  return _this.Get_().(SerializationError_IntTooLarge).I
}

func (_this SerializationError) Dtor_s() _dafny.Sequence {
  return _this.Get_().(SerializationError_StringTooLong).S
}

func (_this SerializationError) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case SerializationError_OutOfMemory: {
      return "Errors.SerializationError.OutOfMemory"
    }
    case SerializationError_IntTooLarge: {
      return "Errors.SerializationError.IntTooLarge" + "(" + _dafny.String(data.I) + ")"
    }
    case SerializationError_StringTooLong: {
      return "Errors.SerializationError.StringTooLong" + "(" + data.S.VerbatimString(true) + ")"
    }
    case SerializationError_InvalidUnicode: {
      return "Errors.SerializationError.InvalidUnicode"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this SerializationError) Equals(other SerializationError) bool {
  switch data1 := _this.Get_().(type) {
    case SerializationError_OutOfMemory: {
      _, ok := other.Get_().(SerializationError_OutOfMemory)
      return ok
    }
    case SerializationError_IntTooLarge: {
      data2, ok := other.Get_().(SerializationError_IntTooLarge)
      return ok && data1.I.Cmp(data2.I) == 0
    }
    case SerializationError_StringTooLong: {
      data2, ok := other.Get_().(SerializationError_StringTooLong)
      return ok && data1.S.Equals(data2.S)
    }
    case SerializationError_InvalidUnicode: {
      _, ok := other.Get_().(SerializationError_InvalidUnicode)
      return ok
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this SerializationError) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(SerializationError)
  return ok && _this.Equals(typed)
}

func Type_SerializationError_() _dafny.TypeDescriptor {
  return type_SerializationError_{}
}

type type_SerializationError_ struct {
}

func (_this type_SerializationError_) Default() interface{} {
  return Companion_SerializationError_.Default();
}

func (_this type_SerializationError_) String() string {
  return "Std_JSON_Errors.SerializationError"
}
func (_this SerializationError) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = SerializationError{}

func (_this SerializationError) ToString() _dafny.Sequence {
  {
    var _source11 SerializationError = _this
    _ = _source11
    if (_source11.Is_OutOfMemory()) {
      return _dafny.UnicodeSeqOfUtf8Bytes("Out of memory")
    } else if (_source11.Is_IntTooLarge()) {
      var _307___mcc_h0 _dafny.Int = _source11.Get_().(SerializationError_IntTooLarge).I
      _ = _307___mcc_h0
      var _308_i _dafny.Int = _307___mcc_h0
      _ = _308_i
      return _dafny.Companion_Sequence_.Concatenate(_dafny.UnicodeSeqOfUtf8Bytes("Integer too large: "), Std_Strings.Companion_Default___.OfInt(_308_i))
    } else if (_source11.Is_StringTooLong()) {
      var _309___mcc_h1 _dafny.Sequence = _source11.Get_().(SerializationError_StringTooLong).S
      _ = _309___mcc_h1
      var _310_s _dafny.Sequence = _309___mcc_h1
      _ = _310_s
      return _dafny.Companion_Sequence_.Concatenate(_dafny.UnicodeSeqOfUtf8Bytes("String too long: "), _310_s)
    } else {
      return _dafny.UnicodeSeqOfUtf8Bytes("Invalid Unicode sequence")
    }
  }
}
// End of datatype SerializationError
