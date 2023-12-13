// Package Std_JSON_Utils_Lexers_Strings
// Dafny module Std_JSON_Utils_Lexers_Strings compiled into Go

package Std_JSON_Utils_Lexers_Strings

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
  return "Std_JSON_Utils_Lexers_Strings.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) StringBody(escaped bool, byte_ int16) Std_JSON_Utils_Lexers_Core.LexerResult {
  if ((byte_) == (int16(_dafny.CodePoint('\\')))) {
    return Std_JSON_Utils_Lexers_Core.Companion_LexerResult_.Create_Partial_(!(escaped))
  } else if (((byte_) == (int16(_dafny.CodePoint('"')))) && (!(escaped))) {
    return Std_JSON_Utils_Lexers_Core.Companion_LexerResult_.Create_Accept_()
  } else {
    return Std_JSON_Utils_Lexers_Core.Companion_LexerResult_.Create_Partial_(false)
  }
}
func (_static *CompanionStruct_Default___) String(st StringLexerState, byte_ int16) Std_JSON_Utils_Lexers_Core.LexerResult {
  var _source13 StringLexerState = st
  _ = _source13
  if (_source13.Is_Start()) {
    if ((byte_) == (int16(_dafny.CodePoint('"')))) {
      return Std_JSON_Utils_Lexers_Core.Companion_LexerResult_.Create_Partial_(Companion_StringLexerState_.Create_Body_(false))
    } else {
      return Std_JSON_Utils_Lexers_Core.Companion_LexerResult_.Create_Reject_(_dafny.UnicodeSeqOfUtf8Bytes("String must start with double quote"))
    }
  } else if (_source13.Is_Body()) {
    var _360___mcc_h0 bool = _source13.Get_().(StringLexerState_Body).Escaped
    _ = _360___mcc_h0
    var _361_escaped bool = _360___mcc_h0
    _ = _361_escaped
    if ((byte_) == (int16(_dafny.CodePoint('\\')))) {
      return Std_JSON_Utils_Lexers_Core.Companion_LexerResult_.Create_Partial_(Companion_StringLexerState_.Create_Body_(!(_361_escaped)))
    } else if (((byte_) == (int16(_dafny.CodePoint('"')))) && (!(_361_escaped))) {
      return Std_JSON_Utils_Lexers_Core.Companion_LexerResult_.Create_Partial_(Companion_StringLexerState_.Create_End_())
    } else {
      return Std_JSON_Utils_Lexers_Core.Companion_LexerResult_.Create_Partial_(Companion_StringLexerState_.Create_Body_(false))
    }
  } else {
    return Std_JSON_Utils_Lexers_Core.Companion_LexerResult_.Create_Accept_()
  }
}
func (_static *CompanionStruct_Default___) StringBodyLexerStart() bool {
  return false
}
func (_static *CompanionStruct_Default___) StringLexerStart() StringLexerState {
  return Companion_StringLexerState_.Create_Start_()
}
// End of class Default__

// Definition of datatype StringLexerState
type StringLexerState struct {
  Data_StringLexerState_
}

func (_this StringLexerState) Get_() Data_StringLexerState_ {
  return _this.Data_StringLexerState_
}

type Data_StringLexerState_ interface {
  isStringLexerState()
}

type CompanionStruct_StringLexerState_ struct {
}
var Companion_StringLexerState_ = CompanionStruct_StringLexerState_ {
}

type StringLexerState_Start struct {
}

func (StringLexerState_Start) isStringLexerState() {}

func (CompanionStruct_StringLexerState_) Create_Start_() StringLexerState {
  return StringLexerState{StringLexerState_Start{}}
}

func (_this StringLexerState) Is_Start() bool {
  _, ok := _this.Get_().(StringLexerState_Start)
  return ok
}

type StringLexerState_Body struct {
  Escaped bool
}

func (StringLexerState_Body) isStringLexerState() {}

func (CompanionStruct_StringLexerState_) Create_Body_(Escaped bool) StringLexerState {
  return StringLexerState{StringLexerState_Body{Escaped}}
}

func (_this StringLexerState) Is_Body() bool {
  _, ok := _this.Get_().(StringLexerState_Body)
  return ok
}

type StringLexerState_End struct {
}

func (StringLexerState_End) isStringLexerState() {}

func (CompanionStruct_StringLexerState_) Create_End_() StringLexerState {
  return StringLexerState{StringLexerState_End{}}
}

func (_this StringLexerState) Is_End() bool {
  _, ok := _this.Get_().(StringLexerState_End)
  return ok
}

func (CompanionStruct_StringLexerState_) Default() StringLexerState {
  return Companion_StringLexerState_.Create_Start_()
}

func (_this StringLexerState) Dtor_escaped() bool {
  return _this.Get_().(StringLexerState_Body).Escaped
}

func (_this StringLexerState) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case StringLexerState_Start: {
      return "Strings.StringLexerState.Start"
    }
    case StringLexerState_Body: {
      return "Strings.StringLexerState.Body" + "(" + _dafny.String(data.Escaped) + ")"
    }
    case StringLexerState_End: {
      return "Strings.StringLexerState.End"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this StringLexerState) Equals(other StringLexerState) bool {
  switch data1 := _this.Get_().(type) {
    case StringLexerState_Start: {
      _, ok := other.Get_().(StringLexerState_Start)
      return ok
    }
    case StringLexerState_Body: {
      data2, ok := other.Get_().(StringLexerState_Body)
      return ok && data1.Escaped == data2.Escaped
    }
    case StringLexerState_End: {
      _, ok := other.Get_().(StringLexerState_End)
      return ok
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this StringLexerState) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(StringLexerState)
  return ok && _this.Equals(typed)
}

func Type_StringLexerState_() _dafny.TypeDescriptor {
  return type_StringLexerState_{}
}

type type_StringLexerState_ struct {
}

func (_this type_StringLexerState_) Default() interface{} {
  return Companion_StringLexerState_.Default();
}

func (_this type_StringLexerState_) String() string {
  return "Std_JSON_Utils_Lexers_Strings.StringLexerState"
}
func (_this StringLexerState) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = StringLexerState{}

// End of datatype StringLexerState
