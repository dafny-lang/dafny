// Package Std_JSON_Deserializer
// Dafny module Std_JSON_Deserializer compiled into Go

package Std_JSON_Deserializer

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
  return "Std_JSON_Deserializer.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) Bool(js Std_JSON_Utils_Views_Core.View__) bool {
  return ((js).At(uint32(0))) == (uint8(_dafny.CodePoint('t')))
}
func (_static *CompanionStruct_Default___) UnsupportedEscape16(code _dafny.Sequence) Std_JSON_Errors.DeserializationError {
  return Std_JSON_Errors.Companion_DeserializationError_.Create_UnsupportedEscape_((Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.FromUTF16Checked(code)).GetOr(_dafny.UnicodeSeqOfUtf8Bytes("Couldn't decode UTF-16")).(_dafny.Sequence))
}
func (_static *CompanionStruct_Default___) ToNat16(str _dafny.Sequence) uint16 {
  var _472_hd _dafny.Int = Std_JSON_Deserializer_Uint16StrConversion.Companion_Default___.ToNat(str)
  _ = _472_hd
  return (_472_hd).Uint16()
}
func (_static *CompanionStruct_Default___) Unescape(str _dafny.Sequence, start _dafny.Int, prefix _dafny.Sequence) Std_Wrappers.Result {
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((start).Cmp(_dafny.IntOfUint32((str).Cardinality())) >= 0) {
    return Std_Wrappers.Companion_Result_.Create_Success_(prefix)
  } else if (((str).Select((start).Uint32()).(uint16)) == (uint16(_dafny.CodePoint('\\')))) {
    if ((_dafny.IntOfUint32((str).Cardinality())).Cmp((start).Plus(_dafny.One)) == 0) {
      return Std_Wrappers.Companion_Result_.Create_Failure_(Std_JSON_Errors.Companion_DeserializationError_.Create_EscapeAtEOS_())
    } else {
      var _473_c uint16 = (str).Select(((start).Plus(_dafny.One)).Uint32()).(uint16)
      _ = _473_c
      if ((_473_c) == (uint16(_dafny.CodePoint('u')))) {
        if ((_dafny.IntOfUint32((str).Cardinality())).Cmp((start).Plus(_dafny.IntOfInt64(6))) <= 0) {
          return Std_Wrappers.Companion_Result_.Create_Failure_(Std_JSON_Errors.Companion_DeserializationError_.Create_EscapeAtEOS_())
        } else {
          var _474_code _dafny.Sequence = (str).Subsequence(((start).Plus(_dafny.IntOfInt64(2))).Uint32(), ((start).Plus(_dafny.IntOfInt64(6))).Uint32())
          _ = _474_code
          if (_dafny.Quantifier((_474_code).UniqueElements(), false, func (_exists_var_0 uint16) bool {
            var _475_c uint16
            _475_c = interface{}(_exists_var_0).(uint16)
            return (_dafny.Companion_Sequence_.Contains(_474_code, _475_c)) && (!(Companion_Default___.HEX__TABLE__16()).Contains(_475_c))
          })) {
            return Std_Wrappers.Companion_Result_.Create_Failure_(Companion_Default___.UnsupportedEscape16(_474_code))
          } else {
            var _476_hd uint16 = Companion_Default___.ToNat16(_474_code)
            _ = _476_hd
            var _in85 _dafny.Sequence = str
            _ = _in85
            var _in86 _dafny.Int = (start).Plus(_dafny.IntOfInt64(6))
            _ = _in86
            var _in87 _dafny.Sequence = _dafny.Companion_Sequence_.Concatenate(prefix, _dafny.SeqOf(_476_hd))
            _ = _in87
            str = _in85
            start = _in86
            prefix = _in87
            goto TAIL_CALL_START
          }
        }
      } else {
        var _477_unescaped uint16 = (func () uint16 { if (_473_c) == (uint16(34)) { return uint16(34) }; return (func () uint16 { if (_473_c) == (uint16(92)) { return uint16(92) }; return (func () uint16 { if (_473_c) == (uint16(98)) { return uint16(8) }; return (func () uint16 { if (_473_c) == (uint16(102)) { return uint16(12) }; return (func () uint16 { if (_473_c) == (uint16(110)) { return uint16(10) }; return (func () uint16 { if (_473_c) == (uint16(114)) { return uint16(13) }; return (func () uint16 { if (_473_c) == (uint16(116)) { return uint16(9) }; return uint16(0) })()  })()  })()  })()  })()  })()  })() 
        _ = _477_unescaped
        if ((_dafny.IntOfUint16(_477_unescaped)).Sign() == 0) {
          return Std_Wrappers.Companion_Result_.Create_Failure_(Companion_Default___.UnsupportedEscape16((str).Subsequence((start).Uint32(), ((start).Plus(_dafny.IntOfInt64(2))).Uint32())))
        } else {
          var _in88 _dafny.Sequence = str
          _ = _in88
          var _in89 _dafny.Int = (start).Plus(_dafny.IntOfInt64(2))
          _ = _in89
          var _in90 _dafny.Sequence = _dafny.Companion_Sequence_.Concatenate(prefix, _dafny.SeqOf(_477_unescaped))
          _ = _in90
          str = _in88
          start = _in89
          prefix = _in90
          goto TAIL_CALL_START
        }
      }
    }
  } else {
    var _in91 _dafny.Sequence = str
    _ = _in91
    var _in92 _dafny.Int = (start).Plus(_dafny.One)
    _ = _in92
    var _in93 _dafny.Sequence = _dafny.Companion_Sequence_.Concatenate(prefix, _dafny.SeqOf((str).Select((start).Uint32()).(uint16)))
    _ = _in93
    str = _in91
    start = _in92
    prefix = _in93
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) String(js Std_JSON_Grammar.Jstring) Std_Wrappers.Result {
  var _478_valueOrError0 Std_Wrappers.Result = (Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.FromUTF8Checked(((js).Dtor_contents()).Bytes())).ToResult(Std_JSON_Errors.Companion_DeserializationError_.Create_InvalidUnicode_())
  _ = _478_valueOrError0
  if ((_478_valueOrError0).IsFailure()) {
    return (_478_valueOrError0).PropagateFailure()
  } else {
    var _479_asUtf32 _dafny.Sequence = (_478_valueOrError0).Extract().(_dafny.Sequence)
    _ = _479_asUtf32
    var _480_valueOrError1 Std_Wrappers.Result = (Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ToUTF16Checked(_479_asUtf32)).ToResult(Std_JSON_Errors.Companion_DeserializationError_.Create_InvalidUnicode_())
    _ = _480_valueOrError1
    if ((_480_valueOrError1).IsFailure()) {
      return (_480_valueOrError1).PropagateFailure()
    } else {
      var _481_asUint16 _dafny.Sequence = (_480_valueOrError1).Extract().(_dafny.Sequence)
      _ = _481_asUint16
      var _482_valueOrError2 Std_Wrappers.Result = Companion_Default___.Unescape(_481_asUint16, _dafny.Zero, _dafny.SeqOf())
      _ = _482_valueOrError2
      if ((_482_valueOrError2).IsFailure()) {
        return (_482_valueOrError2).PropagateFailure()
      } else {
        var _483_unescaped _dafny.Sequence = (_482_valueOrError2).Extract().(_dafny.Sequence)
        _ = _483_unescaped
        return (Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.FromUTF16Checked(_483_unescaped)).ToResult(Std_JSON_Errors.Companion_DeserializationError_.Create_InvalidUnicode_())
      }
    }
  }
}
func (_static *CompanionStruct_Default___) ToInt(sign Std_JSON_Utils_Views_Core.View__, n Std_JSON_Utils_Views_Core.View__) Std_Wrappers.Result {
  var _484_n _dafny.Int = Std_JSON_ByteStrConversion.Companion_Default___.ToNat((n).Bytes())
  _ = _484_n
  return Std_Wrappers.Companion_Result_.Create_Success_((func () _dafny.Int { if (sign).Char_q(_dafny.CodePoint('-')) { return (_dafny.Zero).Minus(_484_n) }; return _484_n })() )
}
func (_static *CompanionStruct_Default___) Number(js Std_JSON_Grammar.Jnumber) Std_Wrappers.Result {
  var _let_tmp_rhs17 Std_JSON_Grammar.Jnumber = js
  _ = _let_tmp_rhs17
  var _485_minus Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs17.Get_().(Std_JSON_Grammar.Jnumber_JNumber).Minus
  _ = _485_minus
  var _486_num Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs17.Get_().(Std_JSON_Grammar.Jnumber_JNumber).Num
  _ = _486_num
  var _487_frac Std_JSON_Grammar.Maybe = _let_tmp_rhs17.Get_().(Std_JSON_Grammar.Jnumber_JNumber).Frac
  _ = _487_frac
  var _488_exp Std_JSON_Grammar.Maybe = _let_tmp_rhs17.Get_().(Std_JSON_Grammar.Jnumber_JNumber).Exp
  _ = _488_exp
  var _489_valueOrError0 Std_Wrappers.Result = Companion_Default___.ToInt(_485_minus, _486_num)
  _ = _489_valueOrError0
  if ((_489_valueOrError0).IsFailure()) {
    return (_489_valueOrError0).PropagateFailure()
  } else {
    var _490_n _dafny.Int = (_489_valueOrError0).Extract().(_dafny.Int)
    _ = _490_n
    var _491_valueOrError1 Std_Wrappers.Result = func (_source17 Std_JSON_Grammar.Maybe) Std_Wrappers.Result {
      if (_source17.Is_Empty()) {
        return Std_Wrappers.Companion_Result_.Create_Success_(_dafny.Zero)
      } else {
        var _492___mcc_h0 Std_JSON_Grammar.Jexp = _source17.Get_().(Std_JSON_Grammar.Maybe_NonEmpty).T.(Std_JSON_Grammar.Jexp)
        _ = _492___mcc_h0
        var _source18 Std_JSON_Grammar.Jexp = _492___mcc_h0
        _ = _source18
        var _493___mcc_h1 Std_JSON_Utils_Views_Core.View__ = _source18.Get_().(Std_JSON_Grammar.Jexp_JExp).E
        _ = _493___mcc_h1
        var _494___mcc_h2 Std_JSON_Utils_Views_Core.View__ = _source18.Get_().(Std_JSON_Grammar.Jexp_JExp).Sign
        _ = _494___mcc_h2
        var _495___mcc_h3 Std_JSON_Utils_Views_Core.View__ = _source18.Get_().(Std_JSON_Grammar.Jexp_JExp).Num
        _ = _495___mcc_h3
        var _496_num Std_JSON_Utils_Views_Core.View__ = _495___mcc_h3
        _ = _496_num
        var _497_sign Std_JSON_Utils_Views_Core.View__ = _494___mcc_h2
        _ = _497_sign
        return Companion_Default___.ToInt(_497_sign, _496_num)
      }
    }(_488_exp)
    _ = _491_valueOrError1
    if ((_491_valueOrError1).IsFailure()) {
      return (_491_valueOrError1).PropagateFailure()
    } else {
      var _498_e10 _dafny.Int = (_491_valueOrError1).Extract().(_dafny.Int)
      _ = _498_e10
      var _source19 Std_JSON_Grammar.Maybe = _487_frac
      _ = _source19
      if (_source19.Is_Empty()) {
        return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Values.Companion_Decimal_.Create_Decimal_(_490_n, _498_e10))
      } else {
        var _499___mcc_h4 Std_JSON_Grammar.Jfrac = _source19.Get_().(Std_JSON_Grammar.Maybe_NonEmpty).T.(Std_JSON_Grammar.Jfrac)
        _ = _499___mcc_h4
        var _source20 Std_JSON_Grammar.Jfrac = _499___mcc_h4
        _ = _source20
        var _500___mcc_h5 Std_JSON_Utils_Views_Core.View__ = _source20.Get_().(Std_JSON_Grammar.Jfrac_JFrac).Period
        _ = _500___mcc_h5
        var _501___mcc_h6 Std_JSON_Utils_Views_Core.View__ = _source20.Get_().(Std_JSON_Grammar.Jfrac_JFrac).Num
        _ = _501___mcc_h6
        var _502_num Std_JSON_Utils_Views_Core.View__ = _501___mcc_h6
        _ = _502_num
        var _503_pow10 _dafny.Int = _dafny.IntOfUint32((_502_num).Length())
        _ = _503_pow10
        var _504_valueOrError2 Std_Wrappers.Result = Companion_Default___.ToInt(_485_minus, _502_num)
        _ = _504_valueOrError2
        if ((_504_valueOrError2).IsFailure()) {
          return (_504_valueOrError2).PropagateFailure()
        } else {
          var _505_frac _dafny.Int = (_504_valueOrError2).Extract().(_dafny.Int)
          _ = _505_frac
          return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Values.Companion_Decimal_.Create_Decimal_(((_490_n).Times(Std_Arithmetic_Power.Companion_Default___.Pow(_dafny.IntOfInt64(10), _503_pow10))).Plus(_505_frac), (_498_e10).Minus(_503_pow10)))
        }
      }
    }
  }
}
func (_static *CompanionStruct_Default___) KeyValue(js Std_JSON_Grammar.JKeyValue) Std_Wrappers.Result {
  var _506_valueOrError0 Std_Wrappers.Result = Companion_Default___.String((js).Dtor_k())
  _ = _506_valueOrError0
  if ((_506_valueOrError0).IsFailure()) {
    return (_506_valueOrError0).PropagateFailure()
  } else {
    var _507_k _dafny.Sequence = (_506_valueOrError0).Extract().(_dafny.Sequence)
    _ = _507_k
    var _508_valueOrError1 Std_Wrappers.Result = Companion_Default___.Value((js).Dtor_v())
    _ = _508_valueOrError1
    if ((_508_valueOrError1).IsFailure()) {
      return (_508_valueOrError1).PropagateFailure()
    } else {
      var _509_v Std_JSON_Values.JSON = (_508_valueOrError1).Extract().(Std_JSON_Values.JSON)
      _ = _509_v
      return Std_Wrappers.Companion_Result_.Create_Success_(_dafny.TupleOf(_507_k, _509_v))
    }
  }
}
func (_static *CompanionStruct_Default___) Object(js Std_JSON_Grammar.Bracketed) Std_Wrappers.Result {
  return Std_Collections_Seq.Companion_Default___.MapWithResult(func (coer32 func (Std_JSON_Grammar.Suffixed) Std_Wrappers.Result) func (interface{}) Std_Wrappers.Result {
    return func (arg34 interface{}) Std_Wrappers.Result {
      return coer32(arg34.(Std_JSON_Grammar.Suffixed))
    }
  }((func (_510_js Std_JSON_Grammar.Bracketed) func (Std_JSON_Grammar.Suffixed) Std_Wrappers.Result {
    return func (_511_d Std_JSON_Grammar.Suffixed) Std_Wrappers.Result {
      return Companion_Default___.KeyValue((_511_d).Dtor_t().(Std_JSON_Grammar.JKeyValue))
    }
  })(js)), (js).Dtor_data())
}
func (_static *CompanionStruct_Default___) Array(js Std_JSON_Grammar.Bracketed) Std_Wrappers.Result {
  return Std_Collections_Seq.Companion_Default___.MapWithResult(func (coer33 func (Std_JSON_Grammar.Suffixed) Std_Wrappers.Result) func (interface{}) Std_Wrappers.Result {
    return func (arg35 interface{}) Std_Wrappers.Result {
      return coer33(arg35.(Std_JSON_Grammar.Suffixed))
    }
  }((func (_512_js Std_JSON_Grammar.Bracketed) func (Std_JSON_Grammar.Suffixed) Std_Wrappers.Result {
    return func (_513_d Std_JSON_Grammar.Suffixed) Std_Wrappers.Result {
      return Companion_Default___.Value((_513_d).Dtor_t().(Std_JSON_Grammar.Value))
    }
  })(js)), (js).Dtor_data())
}
func (_static *CompanionStruct_Default___) Value(js Std_JSON_Grammar.Value) Std_Wrappers.Result {
  var _source21 Std_JSON_Grammar.Value = js
  _ = _source21
  if (_source21.Is_Null()) {
    var _514___mcc_h0 Std_JSON_Utils_Views_Core.View__ = _source21.Get_().(Std_JSON_Grammar.Value_Null).N
    _ = _514___mcc_h0
    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Values.Companion_JSON_.Create_Null_())
  } else if (_source21.Is_Bool()) {
    var _515___mcc_h1 Std_JSON_Utils_Views_Core.View__ = _source21.Get_().(Std_JSON_Grammar.Value_Bool).B
    _ = _515___mcc_h1
    var _516_b Std_JSON_Utils_Views_Core.View__ = _515___mcc_h1
    _ = _516_b
    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Values.Companion_JSON_.Create_Bool_(Companion_Default___.Bool(_516_b)))
  } else if (_source21.Is_String()) {
    var _517___mcc_h2 Std_JSON_Grammar.Jstring = _source21.Get_().(Std_JSON_Grammar.Value_String).Str
    _ = _517___mcc_h2
    var _518_str Std_JSON_Grammar.Jstring = _517___mcc_h2
    _ = _518_str
    var _519_valueOrError0 Std_Wrappers.Result = Companion_Default___.String(_518_str)
    _ = _519_valueOrError0
    if ((_519_valueOrError0).IsFailure()) {
      return (_519_valueOrError0).PropagateFailure()
    } else {
      var _520_s _dafny.Sequence = (_519_valueOrError0).Extract().(_dafny.Sequence)
      _ = _520_s
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Values.Companion_JSON_.Create_String_(_520_s))
    }
  } else if (_source21.Is_Number()) {
    var _521___mcc_h3 Std_JSON_Grammar.Jnumber = _source21.Get_().(Std_JSON_Grammar.Value_Number).Num
    _ = _521___mcc_h3
    var _522_dec Std_JSON_Grammar.Jnumber = _521___mcc_h3
    _ = _522_dec
    var _523_valueOrError1 Std_Wrappers.Result = Companion_Default___.Number(_522_dec)
    _ = _523_valueOrError1
    if ((_523_valueOrError1).IsFailure()) {
      return (_523_valueOrError1).PropagateFailure()
    } else {
      var _524_n Std_JSON_Values.Decimal = (_523_valueOrError1).Extract().(Std_JSON_Values.Decimal)
      _ = _524_n
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Values.Companion_JSON_.Create_Number_(_524_n))
    }
  } else if (_source21.Is_Object()) {
    var _525___mcc_h4 Std_JSON_Grammar.Bracketed = _source21.Get_().(Std_JSON_Grammar.Value_Object).Obj
    _ = _525___mcc_h4
    var _526_obj Std_JSON_Grammar.Bracketed = _525___mcc_h4
    _ = _526_obj
    var _527_valueOrError2 Std_Wrappers.Result = Companion_Default___.Object(_526_obj)
    _ = _527_valueOrError2
    if ((_527_valueOrError2).IsFailure()) {
      return (_527_valueOrError2).PropagateFailure()
    } else {
      var _528_o _dafny.Sequence = (_527_valueOrError2).Extract().(_dafny.Sequence)
      _ = _528_o
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Values.Companion_JSON_.Create_Object_(_528_o))
    }
  } else {
    var _529___mcc_h5 Std_JSON_Grammar.Bracketed = _source21.Get_().(Std_JSON_Grammar.Value_Array).Arr
    _ = _529___mcc_h5
    var _530_arr Std_JSON_Grammar.Bracketed = _529___mcc_h5
    _ = _530_arr
    var _531_valueOrError3 Std_Wrappers.Result = Companion_Default___.Array(_530_arr)
    _ = _531_valueOrError3
    if ((_531_valueOrError3).IsFailure()) {
      return (_531_valueOrError3).PropagateFailure()
    } else {
      var _532_a _dafny.Sequence = (_531_valueOrError3).Extract().(_dafny.Sequence)
      _ = _532_a
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Values.Companion_JSON_.Create_Array_(_532_a))
    }
  }
}
func (_static *CompanionStruct_Default___) JSON(js Std_JSON_Grammar.Structural) Std_Wrappers.Result {
  return Companion_Default___.Value((js).Dtor_t().(Std_JSON_Grammar.Value))
}
func (_static *CompanionStruct_Default___) HEX__TABLE__16() _dafny.Map {
  return Std_JSON_Deserializer_Uint16StrConversion.Companion_Default___.CharToDigit()
}
func (_static *CompanionStruct_Default___) DIGITS() _dafny.Map {
  return Std_JSON_ByteStrConversion.Companion_Default___.CharToDigit()
}
func (_static *CompanionStruct_Default___) MINUS() uint8 {
  return uint8(_dafny.CodePoint('-'))
}
// End of class Default__
