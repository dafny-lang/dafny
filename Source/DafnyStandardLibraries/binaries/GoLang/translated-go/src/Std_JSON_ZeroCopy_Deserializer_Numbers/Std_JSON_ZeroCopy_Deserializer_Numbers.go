// Package Std_JSON_ZeroCopy_Deserializer_Numbers
// Dafny module Std_JSON_ZeroCopy_Deserializer_Numbers compiled into Go

package Std_JSON_ZeroCopy_Deserializer_Numbers

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
  var _629_sp Std_JSON_Utils_Cursors.Split = Companion_Default___.Digits(cs)
  _ = _629_sp
  if (((_629_sp).Dtor_t().(Std_JSON_Utils_Views_Core.View__)).Empty_q()) {
    return Std_Wrappers.Companion_Result_.Create_Failure_(Std_JSON_Utils_Cursors.Companion_CursorError_.Create_OtherError_(Std_JSON_Errors.Companion_DeserializationError_.Create_EmptyNumber_()))
  } else {
    return Std_Wrappers.Companion_Result_.Create_Success_(_629_sp)
  }
}
func (_static *CompanionStruct_Default___) NonZeroInt(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  return Companion_Default___.NonEmptyDigits(cs)
}
func (_static *CompanionStruct_Default___) OptionalMinus(cs Std_JSON_Utils_Cursors.Cursor__) Std_JSON_Utils_Cursors.Split {
  return ((cs).SkipIf(func (_630_c uint8) bool {
    return (_630_c) == (uint8(_dafny.CodePoint('-')))
  })).Split()
}
func (_static *CompanionStruct_Default___) OptionalSign(cs Std_JSON_Utils_Cursors.Cursor__) Std_JSON_Utils_Cursors.Split {
  return ((cs).SkipIf(func (_631_c uint8) bool {
    return ((_631_c) == (uint8(_dafny.CodePoint('-')))) || ((_631_c) == (uint8(_dafny.CodePoint('+'))))
  })).Split()
}
func (_static *CompanionStruct_Default___) TrimmedInt(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  var _632_sp Std_JSON_Utils_Cursors.Split = ((cs).SkipIf(func (_633_c uint8) bool {
    return (_633_c) == (uint8(_dafny.CodePoint('0')))
  })).Split()
  _ = _632_sp
  if (((_632_sp).Dtor_t().(Std_JSON_Utils_Views_Core.View__)).Empty_q()) {
    return Companion_Default___.NonZeroInt((_632_sp).Dtor_cs())
  } else {
    return Std_Wrappers.Companion_Result_.Create_Success_(_632_sp)
  }
}
func (_static *CompanionStruct_Default___) Exp(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  var _let_tmp_rhs27 Std_JSON_Utils_Cursors.Split = ((cs).SkipIf(func (_634_c uint8) bool {
    return ((_634_c) == (uint8(_dafny.CodePoint('e')))) || ((_634_c) == (uint8(_dafny.CodePoint('E'))))
  })).Split()
  _ = _let_tmp_rhs27
  var _635_e Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs27.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
  _ = _635_e
  var _636_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs27.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
  _ = _636_cs
  if ((_635_e).Empty_q()) {
    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(Std_JSON_Grammar.Companion_Maybe_.Create_Empty_(), _636_cs))
  } else {
    var _let_tmp_rhs28 Std_JSON_Utils_Cursors.Split = Companion_Default___.OptionalSign(_636_cs)
    _ = _let_tmp_rhs28
    var _637_sign Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs28.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
    _ = _637_sign
    var _638_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs28.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
    _ = _638_cs
    var _639_valueOrError0 Std_Wrappers.Result = Companion_Default___.NonEmptyDigits(_638_cs)
    _ = _639_valueOrError0
    if ((_639_valueOrError0).IsFailure()) {
      return (_639_valueOrError0).PropagateFailure()
    } else {
      var _let_tmp_rhs29 Std_JSON_Utils_Cursors.Split = (_639_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Split)
      _ = _let_tmp_rhs29
      var _640_num Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs29.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
      _ = _640_num
      var _641_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs29.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
      _ = _641_cs
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(Std_JSON_Grammar.Companion_Maybe_.Create_NonEmpty_(Std_JSON_Grammar.Companion_Jexp_.Create_JExp_(_635_e, _637_sign, _640_num)), _641_cs))
    }
  }
}
func (_static *CompanionStruct_Default___) Frac(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  var _let_tmp_rhs30 Std_JSON_Utils_Cursors.Split = ((cs).SkipIf(func (_642_c uint8) bool {
    return (_642_c) == (uint8(_dafny.CodePoint('.')))
  })).Split()
  _ = _let_tmp_rhs30
  var _643_period Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs30.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
  _ = _643_period
  var _644_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs30.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
  _ = _644_cs
  if ((_643_period).Empty_q()) {
    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(Std_JSON_Grammar.Companion_Maybe_.Create_Empty_(), _644_cs))
  } else {
    var _645_valueOrError0 Std_Wrappers.Result = Companion_Default___.NonEmptyDigits(_644_cs)
    _ = _645_valueOrError0
    if ((_645_valueOrError0).IsFailure()) {
      return (_645_valueOrError0).PropagateFailure()
    } else {
      var _let_tmp_rhs31 Std_JSON_Utils_Cursors.Split = (_645_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Split)
      _ = _let_tmp_rhs31
      var _646_num Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs31.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
      _ = _646_num
      var _647_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs31.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
      _ = _647_cs
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(Std_JSON_Grammar.Companion_Maybe_.Create_NonEmpty_(Std_JSON_Grammar.Companion_Jfrac_.Create_JFrac_(_643_period, _646_num)), _647_cs))
    }
  }
}
func (_static *CompanionStruct_Default___) NumberFromParts(minus Std_JSON_Utils_Cursors.Split, num Std_JSON_Utils_Cursors.Split, frac Std_JSON_Utils_Cursors.Split, exp Std_JSON_Utils_Cursors.Split) Std_JSON_Utils_Cursors.Split {
  var _648_sp Std_JSON_Utils_Cursors.Split = Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(Std_JSON_Grammar.Companion_Jnumber_.Create_JNumber_((minus).Dtor_t().(Std_JSON_Utils_Views_Core.View__), (num).Dtor_t().(Std_JSON_Utils_Views_Core.View__), (frac).Dtor_t().(Std_JSON_Grammar.Maybe), (exp).Dtor_t().(Std_JSON_Grammar.Maybe)), (exp).Dtor_cs())
  _ = _648_sp
  return _648_sp
}
func (_static *CompanionStruct_Default___) Number(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  var _649_minus Std_JSON_Utils_Cursors.Split = Companion_Default___.OptionalMinus(cs)
  _ = _649_minus
  var _650_valueOrError0 Std_Wrappers.Result = Companion_Default___.TrimmedInt((_649_minus).Dtor_cs())
  _ = _650_valueOrError0
  if ((_650_valueOrError0).IsFailure()) {
    return (_650_valueOrError0).PropagateFailure()
  } else {
    var _651_num Std_JSON_Utils_Cursors.Split = (_650_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Split)
    _ = _651_num
    var _652_valueOrError1 Std_Wrappers.Result = Companion_Default___.Frac((_651_num).Dtor_cs())
    _ = _652_valueOrError1
    if ((_652_valueOrError1).IsFailure()) {
      return (_652_valueOrError1).PropagateFailure()
    } else {
      var _653_frac Std_JSON_Utils_Cursors.Split = (_652_valueOrError1).Extract().(Std_JSON_Utils_Cursors.Split)
      _ = _653_frac
      var _654_valueOrError2 Std_Wrappers.Result = Companion_Default___.Exp((_653_frac).Dtor_cs())
      _ = _654_valueOrError2
      if ((_654_valueOrError2).IsFailure()) {
        return (_654_valueOrError2).PropagateFailure()
      } else {
        var _655_exp Std_JSON_Utils_Cursors.Split = (_654_valueOrError2).Extract().(Std_JSON_Utils_Cursors.Split)
        _ = _655_exp
        return Std_Wrappers.Companion_Result_.Create_Success_(Companion_Default___.NumberFromParts(_649_minus, _651_num, _653_frac, _655_exp))
      }
    }
  }
}
// End of class Default__
