// Package Std_JSON_Deserializer
// Dafny module Std_JSON_Deserializer compiled into Go

package Std_JSON_Deserializer

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
  var _480_hd _dafny.Int = Std_JSON_Deserializer_Uint16StrConversion.Companion_Default___.ToNat(str)
  _ = _480_hd
  return (_480_hd).Uint16()
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
      var _481_c uint16 = (str).Select(((start).Plus(_dafny.One)).Uint32()).(uint16)
      _ = _481_c
      if ((_481_c) == (uint16(_dafny.CodePoint('u')))) {
        if ((_dafny.IntOfUint32((str).Cardinality())).Cmp((start).Plus(_dafny.IntOfInt64(6))) <= 0) {
          return Std_Wrappers.Companion_Result_.Create_Failure_(Std_JSON_Errors.Companion_DeserializationError_.Create_EscapeAtEOS_())
        } else {
          var _482_code _dafny.Sequence = (str).Subsequence(((start).Plus(_dafny.IntOfInt64(2))).Uint32(), ((start).Plus(_dafny.IntOfInt64(6))).Uint32())
          _ = _482_code
          if (_dafny.Quantifier((_482_code).UniqueElements(), false, func (_exists_var_0 uint16) bool {
            var _483_c uint16
            _483_c = interface{}(_exists_var_0).(uint16)
            return (_dafny.Companion_Sequence_.Contains(_482_code, _483_c)) && (!(Companion_Default___.HEX__TABLE__16()).Contains(_483_c))
          })) {
            return Std_Wrappers.Companion_Result_.Create_Failure_(Companion_Default___.UnsupportedEscape16(_482_code))
          } else {
            var _484_hd uint16 = Companion_Default___.ToNat16(_482_code)
            _ = _484_hd
            var _in86 _dafny.Sequence = str
            _ = _in86
            var _in87 _dafny.Int = (start).Plus(_dafny.IntOfInt64(6))
            _ = _in87
            var _in88 _dafny.Sequence = _dafny.Companion_Sequence_.Concatenate(prefix, _dafny.SeqOf(_484_hd))
            _ = _in88
            str = _in86
            start = _in87
            prefix = _in88
            goto TAIL_CALL_START
          }
        }
      } else {
        var _485_unescaped uint16 = (func () uint16 { if (_481_c) == (uint16(34)) { return uint16(34) }; return (func () uint16 { if (_481_c) == (uint16(92)) { return uint16(92) }; return (func () uint16 { if (_481_c) == (uint16(98)) { return uint16(8) }; return (func () uint16 { if (_481_c) == (uint16(102)) { return uint16(12) }; return (func () uint16 { if (_481_c) == (uint16(110)) { return uint16(10) }; return (func () uint16 { if (_481_c) == (uint16(114)) { return uint16(13) }; return (func () uint16 { if (_481_c) == (uint16(116)) { return uint16(9) }; return uint16(0) })()  })()  })()  })()  })()  })()  })() 
        _ = _485_unescaped
        if ((_dafny.IntOfUint16(_485_unescaped)).Sign() == 0) {
          return Std_Wrappers.Companion_Result_.Create_Failure_(Companion_Default___.UnsupportedEscape16((str).Subsequence((start).Uint32(), ((start).Plus(_dafny.IntOfInt64(2))).Uint32())))
        } else {
          var _in89 _dafny.Sequence = str
          _ = _in89
          var _in90 _dafny.Int = (start).Plus(_dafny.IntOfInt64(2))
          _ = _in90
          var _in91 _dafny.Sequence = _dafny.Companion_Sequence_.Concatenate(prefix, _dafny.SeqOf(_485_unescaped))
          _ = _in91
          str = _in89
          start = _in90
          prefix = _in91
          goto TAIL_CALL_START
        }
      }
    }
  } else {
    var _in92 _dafny.Sequence = str
    _ = _in92
    var _in93 _dafny.Int = (start).Plus(_dafny.One)
    _ = _in93
    var _in94 _dafny.Sequence = _dafny.Companion_Sequence_.Concatenate(prefix, _dafny.SeqOf((str).Select((start).Uint32()).(uint16)))
    _ = _in94
    str = _in92
    start = _in93
    prefix = _in94
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) String(js Std_JSON_Grammar.Jstring) Std_Wrappers.Result {
  var _486_valueOrError0 Std_Wrappers.Result = (Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.FromUTF8Checked(((js).Dtor_contents()).Bytes())).ToResult(Std_JSON_Errors.Companion_DeserializationError_.Create_InvalidUnicode_())
  _ = _486_valueOrError0
  if ((_486_valueOrError0).IsFailure()) {
    return (_486_valueOrError0).PropagateFailure()
  } else {
    var _487_asUtf32 _dafny.Sequence = (_486_valueOrError0).Extract().(_dafny.Sequence)
    _ = _487_asUtf32
    var _488_valueOrError1 Std_Wrappers.Result = (Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ToUTF16Checked(_487_asUtf32)).ToResult(Std_JSON_Errors.Companion_DeserializationError_.Create_InvalidUnicode_())
    _ = _488_valueOrError1
    if ((_488_valueOrError1).IsFailure()) {
      return (_488_valueOrError1).PropagateFailure()
    } else {
      var _489_asUint16 _dafny.Sequence = (_488_valueOrError1).Extract().(_dafny.Sequence)
      _ = _489_asUint16
      var _490_valueOrError2 Std_Wrappers.Result = Companion_Default___.Unescape(_489_asUint16, _dafny.Zero, _dafny.SeqOf())
      _ = _490_valueOrError2
      if ((_490_valueOrError2).IsFailure()) {
        return (_490_valueOrError2).PropagateFailure()
      } else {
        var _491_unescaped _dafny.Sequence = (_490_valueOrError2).Extract().(_dafny.Sequence)
        _ = _491_unescaped
        return (Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.FromUTF16Checked(_491_unescaped)).ToResult(Std_JSON_Errors.Companion_DeserializationError_.Create_InvalidUnicode_())
      }
    }
  }
}
func (_static *CompanionStruct_Default___) ToInt(sign Std_JSON_Utils_Views_Core.View__, n Std_JSON_Utils_Views_Core.View__) Std_Wrappers.Result {
  var _492_n _dafny.Int = Std_JSON_ByteStrConversion.Companion_Default___.ToNat((n).Bytes())
  _ = _492_n
  return Std_Wrappers.Companion_Result_.Create_Success_((func () _dafny.Int { if (sign).Char_q(_dafny.CodePoint('-')) { return (_dafny.Zero).Minus(_492_n) }; return _492_n })() )
}
func (_static *CompanionStruct_Default___) Number(js Std_JSON_Grammar.Jnumber) Std_Wrappers.Result {
  var _let_tmp_rhs17 Std_JSON_Grammar.Jnumber = js
  _ = _let_tmp_rhs17
  var _493_minus Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs17.Get_().(Std_JSON_Grammar.Jnumber_JNumber).Minus
  _ = _493_minus
  var _494_num Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs17.Get_().(Std_JSON_Grammar.Jnumber_JNumber).Num
  _ = _494_num
  var _495_frac Std_JSON_Grammar.Maybe = _let_tmp_rhs17.Get_().(Std_JSON_Grammar.Jnumber_JNumber).Frac
  _ = _495_frac
  var _496_exp Std_JSON_Grammar.Maybe = _let_tmp_rhs17.Get_().(Std_JSON_Grammar.Jnumber_JNumber).Exp
  _ = _496_exp
  var _497_valueOrError0 Std_Wrappers.Result = Companion_Default___.ToInt(_493_minus, _494_num)
  _ = _497_valueOrError0
  if ((_497_valueOrError0).IsFailure()) {
    return (_497_valueOrError0).PropagateFailure()
  } else {
    var _498_n _dafny.Int = (_497_valueOrError0).Extract().(_dafny.Int)
    _ = _498_n
    var _499_valueOrError1 Std_Wrappers.Result = func (_source17 Std_JSON_Grammar.Maybe) Std_Wrappers.Result {
      if (_source17.Is_Empty()) {
        return Std_Wrappers.Companion_Result_.Create_Success_(_dafny.Zero)
      } else {
        var _500___mcc_h0 Std_JSON_Grammar.Jexp = _source17.Get_().(Std_JSON_Grammar.Maybe_NonEmpty).T.(Std_JSON_Grammar.Jexp)
        _ = _500___mcc_h0
        var _source18 Std_JSON_Grammar.Jexp = _500___mcc_h0
        _ = _source18
        var _501___mcc_h1 Std_JSON_Utils_Views_Core.View__ = _source18.Get_().(Std_JSON_Grammar.Jexp_JExp).E
        _ = _501___mcc_h1
        var _502___mcc_h2 Std_JSON_Utils_Views_Core.View__ = _source18.Get_().(Std_JSON_Grammar.Jexp_JExp).Sign
        _ = _502___mcc_h2
        var _503___mcc_h3 Std_JSON_Utils_Views_Core.View__ = _source18.Get_().(Std_JSON_Grammar.Jexp_JExp).Num
        _ = _503___mcc_h3
        var _504_num Std_JSON_Utils_Views_Core.View__ = _503___mcc_h3
        _ = _504_num
        var _505_sign Std_JSON_Utils_Views_Core.View__ = _502___mcc_h2
        _ = _505_sign
        return Companion_Default___.ToInt(_505_sign, _504_num)
      }
    }(_496_exp)
    _ = _499_valueOrError1
    if ((_499_valueOrError1).IsFailure()) {
      return (_499_valueOrError1).PropagateFailure()
    } else {
      var _506_e10 _dafny.Int = (_499_valueOrError1).Extract().(_dafny.Int)
      _ = _506_e10
      var _source19 Std_JSON_Grammar.Maybe = _495_frac
      _ = _source19
      if (_source19.Is_Empty()) {
        return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Values.Companion_Decimal_.Create_Decimal_(_498_n, _506_e10))
      } else {
        var _507___mcc_h4 Std_JSON_Grammar.Jfrac = _source19.Get_().(Std_JSON_Grammar.Maybe_NonEmpty).T.(Std_JSON_Grammar.Jfrac)
        _ = _507___mcc_h4
        var _source20 Std_JSON_Grammar.Jfrac = _507___mcc_h4
        _ = _source20
        var _508___mcc_h5 Std_JSON_Utils_Views_Core.View__ = _source20.Get_().(Std_JSON_Grammar.Jfrac_JFrac).Period
        _ = _508___mcc_h5
        var _509___mcc_h6 Std_JSON_Utils_Views_Core.View__ = _source20.Get_().(Std_JSON_Grammar.Jfrac_JFrac).Num
        _ = _509___mcc_h6
        var _510_num Std_JSON_Utils_Views_Core.View__ = _509___mcc_h6
        _ = _510_num
        var _511_pow10 _dafny.Int = _dafny.IntOfUint32((_510_num).Length())
        _ = _511_pow10
        var _512_valueOrError2 Std_Wrappers.Result = Companion_Default___.ToInt(_493_minus, _510_num)
        _ = _512_valueOrError2
        if ((_512_valueOrError2).IsFailure()) {
          return (_512_valueOrError2).PropagateFailure()
        } else {
          var _513_frac _dafny.Int = (_512_valueOrError2).Extract().(_dafny.Int)
          _ = _513_frac
          return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Values.Companion_Decimal_.Create_Decimal_(((_498_n).Times(Std_Arithmetic_Power.Companion_Default___.Pow(_dafny.IntOfInt64(10), _511_pow10))).Plus(_513_frac), (_506_e10).Minus(_511_pow10)))
        }
      }
    }
  }
}
func (_static *CompanionStruct_Default___) KeyValue(js Std_JSON_Grammar.JKeyValue) Std_Wrappers.Result {
  var _514_valueOrError0 Std_Wrappers.Result = Companion_Default___.String((js).Dtor_k())
  _ = _514_valueOrError0
  if ((_514_valueOrError0).IsFailure()) {
    return (_514_valueOrError0).PropagateFailure()
  } else {
    var _515_k _dafny.Sequence = (_514_valueOrError0).Extract().(_dafny.Sequence)
    _ = _515_k
    var _516_valueOrError1 Std_Wrappers.Result = Companion_Default___.Value((js).Dtor_v())
    _ = _516_valueOrError1
    if ((_516_valueOrError1).IsFailure()) {
      return (_516_valueOrError1).PropagateFailure()
    } else {
      var _517_v Std_JSON_Values.JSON = (_516_valueOrError1).Extract().(Std_JSON_Values.JSON)
      _ = _517_v
      return Std_Wrappers.Companion_Result_.Create_Success_(_dafny.TupleOf(_515_k, _517_v))
    }
  }
}
func (_static *CompanionStruct_Default___) Object(js Std_JSON_Grammar.Bracketed) Std_Wrappers.Result {
  return Std_Collections_Seq.Companion_Default___.MapWithResult(func (coer34 func (Std_JSON_Grammar.Suffixed) Std_Wrappers.Result) func (interface{}) Std_Wrappers.Result {
    return func (arg36 interface{}) Std_Wrappers.Result {
      return coer34(arg36.(Std_JSON_Grammar.Suffixed))
    }
  }((func (_518_js Std_JSON_Grammar.Bracketed) func (Std_JSON_Grammar.Suffixed) Std_Wrappers.Result {
    return func (_519_d Std_JSON_Grammar.Suffixed) Std_Wrappers.Result {
      return Companion_Default___.KeyValue((_519_d).Dtor_t().(Std_JSON_Grammar.JKeyValue))
    }
  })(js)), (js).Dtor_data())
}
func (_static *CompanionStruct_Default___) Array(js Std_JSON_Grammar.Bracketed) Std_Wrappers.Result {
  return Std_Collections_Seq.Companion_Default___.MapWithResult(func (coer35 func (Std_JSON_Grammar.Suffixed) Std_Wrappers.Result) func (interface{}) Std_Wrappers.Result {
    return func (arg37 interface{}) Std_Wrappers.Result {
      return coer35(arg37.(Std_JSON_Grammar.Suffixed))
    }
  }((func (_520_js Std_JSON_Grammar.Bracketed) func (Std_JSON_Grammar.Suffixed) Std_Wrappers.Result {
    return func (_521_d Std_JSON_Grammar.Suffixed) Std_Wrappers.Result {
      return Companion_Default___.Value((_521_d).Dtor_t().(Std_JSON_Grammar.Value))
    }
  })(js)), (js).Dtor_data())
}
func (_static *CompanionStruct_Default___) Value(js Std_JSON_Grammar.Value) Std_Wrappers.Result {
  var _source21 Std_JSON_Grammar.Value = js
  _ = _source21
  if (_source21.Is_Null()) {
    var _522___mcc_h0 Std_JSON_Utils_Views_Core.View__ = _source21.Get_().(Std_JSON_Grammar.Value_Null).N
    _ = _522___mcc_h0
    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Values.Companion_JSON_.Create_Null_())
  } else if (_source21.Is_Bool()) {
    var _523___mcc_h1 Std_JSON_Utils_Views_Core.View__ = _source21.Get_().(Std_JSON_Grammar.Value_Bool).B
    _ = _523___mcc_h1
    var _524_b Std_JSON_Utils_Views_Core.View__ = _523___mcc_h1
    _ = _524_b
    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Values.Companion_JSON_.Create_Bool_(Companion_Default___.Bool(_524_b)))
  } else if (_source21.Is_String()) {
    var _525___mcc_h2 Std_JSON_Grammar.Jstring = _source21.Get_().(Std_JSON_Grammar.Value_String).Str
    _ = _525___mcc_h2
    var _526_str Std_JSON_Grammar.Jstring = _525___mcc_h2
    _ = _526_str
    var _527_valueOrError0 Std_Wrappers.Result = Companion_Default___.String(_526_str)
    _ = _527_valueOrError0
    if ((_527_valueOrError0).IsFailure()) {
      return (_527_valueOrError0).PropagateFailure()
    } else {
      var _528_s _dafny.Sequence = (_527_valueOrError0).Extract().(_dafny.Sequence)
      _ = _528_s
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Values.Companion_JSON_.Create_String_(_528_s))
    }
  } else if (_source21.Is_Number()) {
    var _529___mcc_h3 Std_JSON_Grammar.Jnumber = _source21.Get_().(Std_JSON_Grammar.Value_Number).Num
    _ = _529___mcc_h3
    var _530_dec Std_JSON_Grammar.Jnumber = _529___mcc_h3
    _ = _530_dec
    var _531_valueOrError1 Std_Wrappers.Result = Companion_Default___.Number(_530_dec)
    _ = _531_valueOrError1
    if ((_531_valueOrError1).IsFailure()) {
      return (_531_valueOrError1).PropagateFailure()
    } else {
      var _532_n Std_JSON_Values.Decimal = (_531_valueOrError1).Extract().(Std_JSON_Values.Decimal)
      _ = _532_n
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Values.Companion_JSON_.Create_Number_(_532_n))
    }
  } else if (_source21.Is_Object()) {
    var _533___mcc_h4 Std_JSON_Grammar.Bracketed = _source21.Get_().(Std_JSON_Grammar.Value_Object).Obj
    _ = _533___mcc_h4
    var _534_obj Std_JSON_Grammar.Bracketed = _533___mcc_h4
    _ = _534_obj
    var _535_valueOrError2 Std_Wrappers.Result = Companion_Default___.Object(_534_obj)
    _ = _535_valueOrError2
    if ((_535_valueOrError2).IsFailure()) {
      return (_535_valueOrError2).PropagateFailure()
    } else {
      var _536_o _dafny.Sequence = (_535_valueOrError2).Extract().(_dafny.Sequence)
      _ = _536_o
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Values.Companion_JSON_.Create_Object_(_536_o))
    }
  } else {
    var _537___mcc_h5 Std_JSON_Grammar.Bracketed = _source21.Get_().(Std_JSON_Grammar.Value_Array).Arr
    _ = _537___mcc_h5
    var _538_arr Std_JSON_Grammar.Bracketed = _537___mcc_h5
    _ = _538_arr
    var _539_valueOrError3 Std_Wrappers.Result = Companion_Default___.Array(_538_arr)
    _ = _539_valueOrError3
    if ((_539_valueOrError3).IsFailure()) {
      return (_539_valueOrError3).PropagateFailure()
    } else {
      var _540_a _dafny.Sequence = (_539_valueOrError3).Extract().(_dafny.Sequence)
      _ = _540_a
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Values.Companion_JSON_.Create_Array_(_540_a))
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
