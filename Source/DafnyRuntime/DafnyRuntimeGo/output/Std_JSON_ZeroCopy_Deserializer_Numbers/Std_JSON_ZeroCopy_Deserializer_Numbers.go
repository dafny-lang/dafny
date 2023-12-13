// Package Std_JSON_ZeroCopy_Deserializer_Numbers
// Dafny module Std_JSON_ZeroCopy_Deserializer_Numbers compiled into Go

package Std_JSON_ZeroCopy_Deserializer_Numbers

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
  return "Std_JSON_ZeroCopy_Deserializer_Numbers.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) Digits(cs Std_JSON_Utils_Cursors.Cursor__) Std_JSON_Utils_Cursors.Split {
  return ((cs).SkipWhile(Std_JSON_Grammar.Companion_Default___.Digit_q)).Split()
}
func (_static *CompanionStruct_Default___) NonEmptyDigits(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  var _637_sp Std_JSON_Utils_Cursors.Split = Companion_Default___.Digits(cs)
  _ = _637_sp
  if (((_637_sp).Dtor_t().(Std_JSON_Utils_Views_Core.View__)).Empty_q()) {
    return Std_Wrappers.Companion_Result_.Create_Failure_(Std_JSON_Utils_Cursors.Companion_CursorError_.Create_OtherError_(Std_JSON_Errors.Companion_DeserializationError_.Create_EmptyNumber_()))
  } else {
    return Std_Wrappers.Companion_Result_.Create_Success_(_637_sp)
  }
}
func (_static *CompanionStruct_Default___) NonZeroInt(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  return Companion_Default___.NonEmptyDigits(cs)
}
func (_static *CompanionStruct_Default___) OptionalMinus(cs Std_JSON_Utils_Cursors.Cursor__) Std_JSON_Utils_Cursors.Split {
  return ((cs).SkipIf(func (_638_c uint8) bool {
    return (_638_c) == (uint8(_dafny.CodePoint('-')))
  })).Split()
}
func (_static *CompanionStruct_Default___) OptionalSign(cs Std_JSON_Utils_Cursors.Cursor__) Std_JSON_Utils_Cursors.Split {
  return ((cs).SkipIf(func (_639_c uint8) bool {
    return ((_639_c) == (uint8(_dafny.CodePoint('-')))) || ((_639_c) == (uint8(_dafny.CodePoint('+'))))
  })).Split()
}
func (_static *CompanionStruct_Default___) TrimmedInt(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  var _640_sp Std_JSON_Utils_Cursors.Split = ((cs).SkipIf(func (_641_c uint8) bool {
    return (_641_c) == (uint8(_dafny.CodePoint('0')))
  })).Split()
  _ = _640_sp
  if (((_640_sp).Dtor_t().(Std_JSON_Utils_Views_Core.View__)).Empty_q()) {
    return Companion_Default___.NonZeroInt((_640_sp).Dtor_cs())
  } else {
    return Std_Wrappers.Companion_Result_.Create_Success_(_640_sp)
  }
}
func (_static *CompanionStruct_Default___) Exp(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  var _let_tmp_rhs27 Std_JSON_Utils_Cursors.Split = ((cs).SkipIf(func (_642_c uint8) bool {
    return ((_642_c) == (uint8(_dafny.CodePoint('e')))) || ((_642_c) == (uint8(_dafny.CodePoint('E'))))
  })).Split()
  _ = _let_tmp_rhs27
  var _643_e Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs27.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
  _ = _643_e
  var _644_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs27.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
  _ = _644_cs
  if ((_643_e).Empty_q()) {
    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(Std_JSON_Grammar.Companion_Maybe_.Create_Empty_(), _644_cs))
  } else {
    var _let_tmp_rhs28 Std_JSON_Utils_Cursors.Split = Companion_Default___.OptionalSign(_644_cs)
    _ = _let_tmp_rhs28
    var _645_sign Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs28.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
    _ = _645_sign
    var _646_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs28.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
    _ = _646_cs
    var _647_valueOrError0 Std_Wrappers.Result = Companion_Default___.NonEmptyDigits(_646_cs)
    _ = _647_valueOrError0
    if ((_647_valueOrError0).IsFailure()) {
      return (_647_valueOrError0).PropagateFailure()
    } else {
      var _let_tmp_rhs29 Std_JSON_Utils_Cursors.Split = (_647_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Split)
      _ = _let_tmp_rhs29
      var _648_num Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs29.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
      _ = _648_num
      var _649_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs29.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
      _ = _649_cs
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(Std_JSON_Grammar.Companion_Maybe_.Create_NonEmpty_(Std_JSON_Grammar.Companion_Jexp_.Create_JExp_(_643_e, _645_sign, _648_num)), _649_cs))
    }
  }
}
func (_static *CompanionStruct_Default___) Frac(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  var _let_tmp_rhs30 Std_JSON_Utils_Cursors.Split = ((cs).SkipIf(func (_650_c uint8) bool {
    return (_650_c) == (uint8(_dafny.CodePoint('.')))
  })).Split()
  _ = _let_tmp_rhs30
  var _651_period Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs30.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
  _ = _651_period
  var _652_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs30.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
  _ = _652_cs
  if ((_651_period).Empty_q()) {
    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(Std_JSON_Grammar.Companion_Maybe_.Create_Empty_(), _652_cs))
  } else {
    var _653_valueOrError0 Std_Wrappers.Result = Companion_Default___.NonEmptyDigits(_652_cs)
    _ = _653_valueOrError0
    if ((_653_valueOrError0).IsFailure()) {
      return (_653_valueOrError0).PropagateFailure()
    } else {
      var _let_tmp_rhs31 Std_JSON_Utils_Cursors.Split = (_653_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Split)
      _ = _let_tmp_rhs31
      var _654_num Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs31.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
      _ = _654_num
      var _655_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs31.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
      _ = _655_cs
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(Std_JSON_Grammar.Companion_Maybe_.Create_NonEmpty_(Std_JSON_Grammar.Companion_Jfrac_.Create_JFrac_(_651_period, _654_num)), _655_cs))
    }
  }
}
func (_static *CompanionStruct_Default___) NumberFromParts(minus Std_JSON_Utils_Cursors.Split, num Std_JSON_Utils_Cursors.Split, frac Std_JSON_Utils_Cursors.Split, exp Std_JSON_Utils_Cursors.Split) Std_JSON_Utils_Cursors.Split {
  var _656_sp Std_JSON_Utils_Cursors.Split = Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(Std_JSON_Grammar.Companion_Jnumber_.Create_JNumber_((minus).Dtor_t().(Std_JSON_Utils_Views_Core.View__), (num).Dtor_t().(Std_JSON_Utils_Views_Core.View__), (frac).Dtor_t().(Std_JSON_Grammar.Maybe), (exp).Dtor_t().(Std_JSON_Grammar.Maybe)), (exp).Dtor_cs())
  _ = _656_sp
  return _656_sp
}
func (_static *CompanionStruct_Default___) Number(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  var _657_minus Std_JSON_Utils_Cursors.Split = Companion_Default___.OptionalMinus(cs)
  _ = _657_minus
  var _658_valueOrError0 Std_Wrappers.Result = Companion_Default___.TrimmedInt((_657_minus).Dtor_cs())
  _ = _658_valueOrError0
  if ((_658_valueOrError0).IsFailure()) {
    return (_658_valueOrError0).PropagateFailure()
  } else {
    var _659_num Std_JSON_Utils_Cursors.Split = (_658_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Split)
    _ = _659_num
    var _660_valueOrError1 Std_Wrappers.Result = Companion_Default___.Frac((_659_num).Dtor_cs())
    _ = _660_valueOrError1
    if ((_660_valueOrError1).IsFailure()) {
      return (_660_valueOrError1).PropagateFailure()
    } else {
      var _661_frac Std_JSON_Utils_Cursors.Split = (_660_valueOrError1).Extract().(Std_JSON_Utils_Cursors.Split)
      _ = _661_frac
      var _662_valueOrError2 Std_Wrappers.Result = Companion_Default___.Exp((_661_frac).Dtor_cs())
      _ = _662_valueOrError2
      if ((_662_valueOrError2).IsFailure()) {
        return (_662_valueOrError2).PropagateFailure()
      } else {
        var _663_exp Std_JSON_Utils_Cursors.Split = (_662_valueOrError2).Extract().(Std_JSON_Utils_Cursors.Split)
        _ = _663_exp
        return Std_Wrappers.Companion_Result_.Create_Success_(Companion_Default___.NumberFromParts(_657_minus, _659_num, _661_frac, _663_exp))
      }
    }
  }
}
// End of class Default__
