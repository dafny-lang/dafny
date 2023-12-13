// Package Std_JSON_ZeroCopy_Deserializer_API
// Dafny module Std_JSON_ZeroCopy_Deserializer_API compiled into Go

package Std_JSON_ZeroCopy_Deserializer_API

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
  Std_JSON_Utils_Cursors "Std_JSON_Utils_Cursors"
  Std_JSON_Utils_Parsers "Std_JSON_Utils_Parsers"
  Std_JSON_Utils "Std_JSON_Utils"
  Std_JSON_Grammar "Std_JSON_Grammar"
  Std_JSON_ByteStrConversion "Std_JSON_ByteStrConversion"
  Std_JSON_Serializer "Std_JSON_Serializer"
  Std_JSON_Deserializer_Uint16StrConversion "Std_JSON_Deserializer_Uint16StrConversion"
  Std_JSON_Deserializer "Std_JSON_Deserializer"
  Std_JSON_ConcreteSyntax_Spec "Std_JSON_ConcreteSyntax_Spec"
  Std_JSON_ConcreteSyntax_SpecProperties "Std_JSON_ConcreteSyntax_SpecProperties"
  Std_JSON_ConcreteSyntax "Std_JSON_ConcreteSyntax"
  Std_JSON_ZeroCopy_Serializer "Std_JSON_ZeroCopy_Serializer"
  Std_JSON_ZeroCopy_Deserializer_Core "Std_JSON_ZeroCopy_Deserializer_Core"
  Std_JSON_ZeroCopy_Deserializer_Strings "Std_JSON_ZeroCopy_Deserializer_Strings"
  Std_JSON_ZeroCopy_Deserializer_Numbers "Std_JSON_ZeroCopy_Deserializer_Numbers"
  Std_JSON_ZeroCopy_Deserializer_ObjectParams "Std_JSON_ZeroCopy_Deserializer_ObjectParams"
  Std_JSON_ZeroCopy_Deserializer_Objects "Std_JSON_ZeroCopy_Deserializer_Objects"
  Std_JSON_ZeroCopy_Deserializer_ArrayParams "Std_JSON_ZeroCopy_Deserializer_ArrayParams"
  Std_JSON_ZeroCopy_Deserializer_Arrays "Std_JSON_ZeroCopy_Deserializer_Arrays"
  Std_JSON_ZeroCopy_Deserializer_Constants "Std_JSON_ZeroCopy_Deserializer_Constants"
  Std_JSON_ZeroCopy_Deserializer_Values "Std_JSON_ZeroCopy_Deserializer_Values"
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
var _ Std_JSON_Utils_Views_Writers.Dummy__
var _ Std_JSON_Utils_Views.Dummy__
var _ Std_JSON_Utils_Lexers_Core.Dummy__
var _ Std_JSON_Utils_Lexers_Strings.Dummy__
var _ Std_JSON_Utils_Lexers.Dummy__
var _ Std_JSON_Utils_Cursors.Dummy__
var _ Std_JSON_Utils_Parsers.Dummy__
var _ Std_JSON_Utils.Dummy__
var _ Std_JSON_Grammar.Dummy__
var _ Std_JSON_ByteStrConversion.Dummy__
var _ Std_JSON_Serializer.Dummy__
var _ Std_JSON_Deserializer_Uint16StrConversion.Dummy__
var _ Std_JSON_Deserializer.Dummy__
var _ Std_JSON_ConcreteSyntax_Spec.Dummy__
var _ Std_JSON_ConcreteSyntax_SpecProperties.Dummy__
var _ Std_JSON_ConcreteSyntax.Dummy__
var _ Std_JSON_ZeroCopy_Serializer.Dummy__
var _ Std_JSON_ZeroCopy_Deserializer_Core.Dummy__
var _ Std_JSON_ZeroCopy_Deserializer_Strings.Dummy__
var _ Std_JSON_ZeroCopy_Deserializer_Numbers.Dummy__
var _ Std_JSON_ZeroCopy_Deserializer_ObjectParams.Dummy__
var _ Std_JSON_ZeroCopy_Deserializer_Objects.Dummy__
var _ Std_JSON_ZeroCopy_Deserializer_ArrayParams.Dummy__
var _ Std_JSON_ZeroCopy_Deserializer_Arrays.Dummy__
var _ Std_JSON_ZeroCopy_Deserializer_Constants.Dummy__
var _ Std_JSON_ZeroCopy_Deserializer_Values.Dummy__

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
  return "Std_JSON_ZeroCopy_Deserializer_API.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) LiftCursorError(err Std_JSON_Utils_Cursors.CursorError) Std_JSON_Errors.DeserializationError {
  var _source24 Std_JSON_Utils_Cursors.CursorError = err
  _ = _source24
  if (_source24.Is_EOF()) {
    return Std_JSON_Errors.Companion_DeserializationError_.Create_ReachedEOF_()
  } else if (_source24.Is_ExpectingByte()) {
    var _767___mcc_h0 uint8 = _source24.Get_().(Std_JSON_Utils_Cursors.CursorError_ExpectingByte).Expected
    _ = _767___mcc_h0
    var _768___mcc_h1 int16 = _source24.Get_().(Std_JSON_Utils_Cursors.CursorError_ExpectingByte).B
    _ = _768___mcc_h1
    var _769_b int16 = _768___mcc_h1
    _ = _769_b
    var _770_expected uint8 = _767___mcc_h0
    _ = _770_expected
    return Std_JSON_Errors.Companion_DeserializationError_.Create_ExpectingByte_(_770_expected, _769_b)
  } else if (_source24.Is_ExpectingAnyByte()) {
    var _771___mcc_h2 _dafny.Sequence = _source24.Get_().(Std_JSON_Utils_Cursors.CursorError_ExpectingAnyByte).Expected__sq
    _ = _771___mcc_h2
    var _772___mcc_h3 int16 = _source24.Get_().(Std_JSON_Utils_Cursors.CursorError_ExpectingAnyByte).B
    _ = _772___mcc_h3
    var _773_b int16 = _772___mcc_h3
    _ = _773_b
    var _774_expected__sq _dafny.Sequence = _771___mcc_h2
    _ = _774_expected__sq
    return Std_JSON_Errors.Companion_DeserializationError_.Create_ExpectingAnyByte_(_774_expected__sq, _773_b)
  } else {
    var _775___mcc_h4 Std_JSON_Errors.DeserializationError = _source24.Get_().(Std_JSON_Utils_Cursors.CursorError_OtherError).Err.(Std_JSON_Errors.DeserializationError)
    _ = _775___mcc_h4
    var _776_err Std_JSON_Errors.DeserializationError = _775___mcc_h4
    _ = _776_err
    return _776_err
  }
}
func (_static *CompanionStruct_Default___) JSON(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  return (Std_JSON_ZeroCopy_Deserializer_Core.Companion_Default___.Structural(cs, func (coer49 func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result) func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
    return func (arg51 Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
      return coer49(arg51)
    }
  }(Std_JSON_ZeroCopy_Deserializer_Values.Companion_Default___.Value))).MapFailure(func (coer50 func (Std_JSON_Utils_Cursors.CursorError) Std_JSON_Errors.DeserializationError) func (interface{}) interface{} {
    return func (arg52 interface{}) interface{} {
      return coer50(arg52.(Std_JSON_Utils_Cursors.CursorError))
    }
  }(Companion_Default___.LiftCursorError))
}
func (_static *CompanionStruct_Default___) Text(v Std_JSON_Utils_Views_Core.View__) Std_Wrappers.Result {
  var _777_valueOrError0 Std_Wrappers.Result = Companion_Default___.JSON(Std_JSON_Utils_Cursors.Companion_Cursor___.OfView(v))
  _ = _777_valueOrError0
  if ((_777_valueOrError0).IsFailure()) {
    return (_777_valueOrError0).PropagateFailure()
  } else {
    var _let_tmp_rhs39 Std_JSON_Utils_Cursors.Split = (_777_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Split)
    _ = _let_tmp_rhs39
    var _778_text Std_JSON_Grammar.Structural = _let_tmp_rhs39.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Grammar.Structural)
    _ = _778_text
    var _779_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs39.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
    _ = _779_cs
    var _780_valueOrError1 Std_Wrappers.OutcomeResult = Std_Wrappers.Companion_Default___.Need((_779_cs).EOF_q(), Std_JSON_Errors.Companion_DeserializationError_.Create_ExpectingEOF_())
    _ = _780_valueOrError1
    if ((_780_valueOrError1).IsFailure()) {
      return (_780_valueOrError1).PropagateFailure()
    } else {
      return Std_Wrappers.Companion_Result_.Create_Success_(_778_text)
    }
  }
}
func (_static *CompanionStruct_Default___) OfBytes(bs _dafny.Sequence) Std_Wrappers.Result {
  var _781_valueOrError0 Std_Wrappers.OutcomeResult = Std_Wrappers.Companion_Default___.Need((_dafny.IntOfUint32((bs).Cardinality())).Cmp(Std_BoundedInts.Companion_Default___.TWO__TO__THE__32()) < 0, Std_JSON_Errors.Companion_DeserializationError_.Create_IntOverflow_())
  _ = _781_valueOrError0
  if ((_781_valueOrError0).IsFailure()) {
    return (_781_valueOrError0).PropagateFailure()
  } else {
    return Companion_Default___.Text(Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(bs))
  }
}
// End of class Default__
