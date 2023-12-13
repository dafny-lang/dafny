// Package Std_JSON_API
// Dafny module Std_JSON_API compiled into Go

package Std_JSON_API

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
  Std_JSON_ZeroCopy_Deserializer_API "Std_JSON_ZeroCopy_Deserializer_API"
  Std_JSON_ZeroCopy_Deserializer "Std_JSON_ZeroCopy_Deserializer"
  Std_JSON_ZeroCopy_API "Std_JSON_ZeroCopy_API"
  Std_JSON_ZeroCopy "Std_JSON_ZeroCopy"
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
var _ Std_JSON_ZeroCopy_Deserializer_API.Dummy__
var _ Std_JSON_ZeroCopy_Deserializer.Dummy__
var _ Std_JSON_ZeroCopy_API.Dummy__
var _ Std_JSON_ZeroCopy.Dummy__

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
  return "Std_JSON_API.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) Serialize(js Std_JSON_Values.JSON) Std_Wrappers.Result {
  var _782_valueOrError0 Std_Wrappers.Result = Std_JSON_Serializer.Companion_Default___.JSON(js)
  _ = _782_valueOrError0
  if ((_782_valueOrError0).IsFailure()) {
    return (_782_valueOrError0).PropagateFailure()
  } else {
    var _783_js Std_JSON_Grammar.Structural = (_782_valueOrError0).Extract().(Std_JSON_Grammar.Structural)
    _ = _783_js
    return Std_JSON_ZeroCopy_API.Companion_Default___.Serialize(_783_js)
  }
}
func (_static *CompanionStruct_Default___) SerializeAlloc(js Std_JSON_Values.JSON) Std_Wrappers.Result {
  var bs Std_Wrappers.Result = Std_Wrappers.Companion_Result_.Default(_dafny.NewArrayWithValue(nil, _dafny.IntOf(0)))
  _ = bs
  var _784_js Std_JSON_Grammar.Structural
  _ = _784_js
  var _785_valueOrError0 Std_Wrappers.Result = Std_Wrappers.Companion_Result_.Default(Std_JSON_Grammar.Companion_Structural_.Default(Std_JSON_Grammar.Companion_Value_.Default()))
  _ = _785_valueOrError0
  _785_valueOrError0 = Std_JSON_Serializer.Companion_Default___.JSON(js)
  if ((_785_valueOrError0).IsFailure()) {
    bs = (_785_valueOrError0).PropagateFailure()
    return bs
  }
  _784_js = (_785_valueOrError0).Extract().(Std_JSON_Grammar.Structural)
  var _out11 Std_Wrappers.Result
  _ = _out11
  _out11 = Std_JSON_ZeroCopy_API.Companion_Default___.SerializeAlloc(_784_js)
  bs = _out11
  return bs
}
func (_static *CompanionStruct_Default___) SerializeInto(js Std_JSON_Values.JSON, bs _dafny.Array) Std_Wrappers.Result {
  var len_ Std_Wrappers.Result = Std_Wrappers.Companion_Result_.Default(uint32(0))
  _ = len_
  var _786_js Std_JSON_Grammar.Structural
  _ = _786_js
  var _787_valueOrError0 Std_Wrappers.Result = Std_Wrappers.Companion_Result_.Default(Std_JSON_Grammar.Companion_Structural_.Default(Std_JSON_Grammar.Companion_Value_.Default()))
  _ = _787_valueOrError0
  _787_valueOrError0 = Std_JSON_Serializer.Companion_Default___.JSON(js)
  if ((_787_valueOrError0).IsFailure()) {
    len_ = (_787_valueOrError0).PropagateFailure()
    return len_
  }
  _786_js = (_787_valueOrError0).Extract().(Std_JSON_Grammar.Structural)
  var _out12 Std_Wrappers.Result
  _ = _out12
  _out12 = Std_JSON_ZeroCopy_API.Companion_Default___.SerializeInto(_786_js, bs)
  len_ = _out12
  return len_
}
func (_static *CompanionStruct_Default___) Deserialize(bs _dafny.Sequence) Std_Wrappers.Result {
  var _788_valueOrError0 Std_Wrappers.Result = Std_JSON_ZeroCopy_API.Companion_Default___.Deserialize(bs)
  _ = _788_valueOrError0
  if ((_788_valueOrError0).IsFailure()) {
    return (_788_valueOrError0).PropagateFailure()
  } else {
    var _789_js Std_JSON_Grammar.Structural = (_788_valueOrError0).Extract().(Std_JSON_Grammar.Structural)
    _ = _789_js
    return Std_JSON_Deserializer.Companion_Default___.JSON(_789_js)
  }
}
// End of class Default__
