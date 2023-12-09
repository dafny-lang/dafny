// Package Std_JSON_ZeroCopy_Deserializer_API
// Dafny module Std_JSON_ZeroCopy_Deserializer_API compiled into Go

package Std_JSON_ZeroCopy_Deserializer_API

import (
  _dafny "dafny"
  os "os"
  _System "System_"
  Std_Wrappers "Std_Wrappers"
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
  DafnyStdLibs_Concurrent "DafnyStdLibs_Concurrent"
  DafnyStdLibs_FileIOInternalExterns "DafnyStdLibs_FileIOInternalExterns"
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
var _ DafnyStdLibs_Concurrent.Dummy__
var _ = DafnyStdLibs_FileIOInternalExterns.INTERNAL__ReadBytesFromFile
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
    var _759___mcc_h0 uint8 = _source24.Get_().(Std_JSON_Utils_Cursors.CursorError_ExpectingByte).Expected
    _ = _759___mcc_h0
    var _760___mcc_h1 int16 = _source24.Get_().(Std_JSON_Utils_Cursors.CursorError_ExpectingByte).B
    _ = _760___mcc_h1
    var _761_b int16 = _760___mcc_h1
    _ = _761_b
    var _762_expected uint8 = _759___mcc_h0
    _ = _762_expected
    return Std_JSON_Errors.Companion_DeserializationError_.Create_ExpectingByte_(_762_expected, _761_b)
  } else if (_source24.Is_ExpectingAnyByte()) {
    var _763___mcc_h2 _dafny.Sequence = _source24.Get_().(Std_JSON_Utils_Cursors.CursorError_ExpectingAnyByte).Expected__sq
    _ = _763___mcc_h2
    var _764___mcc_h3 int16 = _source24.Get_().(Std_JSON_Utils_Cursors.CursorError_ExpectingAnyByte).B
    _ = _764___mcc_h3
    var _765_b int16 = _764___mcc_h3
    _ = _765_b
    var _766_expected__sq _dafny.Sequence = _763___mcc_h2
    _ = _766_expected__sq
    return Std_JSON_Errors.Companion_DeserializationError_.Create_ExpectingAnyByte_(_766_expected__sq, _765_b)
  } else {
    var _767___mcc_h4 Std_JSON_Errors.DeserializationError = _source24.Get_().(Std_JSON_Utils_Cursors.CursorError_OtherError).Err.(Std_JSON_Errors.DeserializationError)
    _ = _767___mcc_h4
    var _768_err Std_JSON_Errors.DeserializationError = _767___mcc_h4
    _ = _768_err
    return _768_err
  }
}
func (_static *CompanionStruct_Default___) JSON(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  return (Std_JSON_ZeroCopy_Deserializer_Core.Companion_Default___.Structural(cs, func (coer47 func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result) func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
    return func (arg49 Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
      return coer47(arg49)
    }
  }(Std_JSON_ZeroCopy_Deserializer_Values.Companion_Default___.Value))).MapFailure(func (coer48 func (Std_JSON_Utils_Cursors.CursorError) Std_JSON_Errors.DeserializationError) func (interface{}) interface{} {
    return func (arg50 interface{}) interface{} {
      return coer48(arg50.(Std_JSON_Utils_Cursors.CursorError))
    }
  }(Companion_Default___.LiftCursorError))
}
func (_static *CompanionStruct_Default___) Text(v Std_JSON_Utils_Views_Core.View__) Std_Wrappers.Result {
  var _769_valueOrError0 Std_Wrappers.Result = Companion_Default___.JSON(Std_JSON_Utils_Cursors.Companion_Cursor___.OfView(v))
  _ = _769_valueOrError0
  if ((_769_valueOrError0).IsFailure()) {
    return (_769_valueOrError0).PropagateFailure()
  } else {
    var _let_tmp_rhs39 Std_JSON_Utils_Cursors.Split = (_769_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Split)
    _ = _let_tmp_rhs39
    var _770_text Std_JSON_Grammar.Structural = _let_tmp_rhs39.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Grammar.Structural)
    _ = _770_text
    var _771_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs39.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
    _ = _771_cs
    var _772_valueOrError1 Std_Wrappers.OutcomeResult = Std_Wrappers.Companion_Default___.Need((_771_cs).EOF_q(), Std_JSON_Errors.Companion_DeserializationError_.Create_ExpectingEOF_())
    _ = _772_valueOrError1
    if ((_772_valueOrError1).IsFailure()) {
      return (_772_valueOrError1).PropagateFailure()
    } else {
      return Std_Wrappers.Companion_Result_.Create_Success_(_770_text)
    }
  }
}
func (_static *CompanionStruct_Default___) OfBytes(bs _dafny.Sequence) Std_Wrappers.Result {
  var _773_valueOrError0 Std_Wrappers.OutcomeResult = Std_Wrappers.Companion_Default___.Need((_dafny.IntOfUint32((bs).Cardinality())).Cmp(Std_BoundedInts.Companion_Default___.TWO__TO__THE__32()) < 0, Std_JSON_Errors.Companion_DeserializationError_.Create_IntOverflow_())
  _ = _773_valueOrError0
  if ((_773_valueOrError0).IsFailure()) {
    return (_773_valueOrError0).PropagateFailure()
  } else {
    return Companion_Default___.Text(Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(bs))
  }
}
// End of class Default__
