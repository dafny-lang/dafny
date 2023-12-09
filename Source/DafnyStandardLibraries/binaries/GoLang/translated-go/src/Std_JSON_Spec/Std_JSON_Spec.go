// Package Std_JSON_Spec
// Dafny module Std_JSON_Spec compiled into Go

package Std_JSON_Spec

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
  return "Std_JSON_Spec.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) EscapeUnicode(c uint16) _dafny.Sequence {
  var _303_sStr _dafny.Sequence = Std_Strings_HexConversion.Companion_Default___.OfNat(_dafny.IntOfUint16(c))
  _ = _303_sStr
  var _304_s _dafny.Sequence = Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF16(_303_sStr)
  _ = _304_s
  return _dafny.Companion_Sequence_.Concatenate(_304_s, _dafny.SeqCreate(((_dafny.IntOfInt64(4)).Minus(_dafny.IntOfUint32((_304_s).Cardinality()))).Uint32(), func (coer23 func (_dafny.Int) uint16) func (_dafny.Int) interface{} {
    return func (arg25 _dafny.Int) interface{} {
      return coer23(arg25)
    }
  }(func (_305___v8 _dafny.Int) uint16 {
    return uint16(_dafny.CodePoint(' '))
  })))
}
func (_static *CompanionStruct_Default___) Escape(str _dafny.Sequence, start _dafny.Int) _dafny.Sequence {
  var _306___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _306___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  var _pat_let_tv0 = str
  _ = _pat_let_tv0
  var _pat_let_tv1 = start
  _ = _pat_let_tv1
  if ((start).Cmp(_dafny.IntOfUint32((str).Cardinality())) >= 0) {
    return _dafny.Companion_Sequence_.Concatenate(_306___accumulator, _dafny.SeqOf())
  } else {
    _306___accumulator = _dafny.Companion_Sequence_.Concatenate(_306___accumulator, (func () _dafny.Sequence { if ((str).Select((start).Uint32()).(uint16)) == (uint16(34)) { return Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF16(_dafny.UnicodeSeqOfUtf8Bytes("\\\"")) }; return (func () _dafny.Sequence { if ((str).Select((start).Uint32()).(uint16)) == (uint16(92)) { return Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF16(_dafny.UnicodeSeqOfUtf8Bytes("\\\\")) }; return (func () _dafny.Sequence { if ((str).Select((start).Uint32()).(uint16)) == (uint16(8)) { return Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF16(_dafny.UnicodeSeqOfUtf8Bytes("\\b")) }; return (func () _dafny.Sequence { if ((str).Select((start).Uint32()).(uint16)) == (uint16(12)) { return Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF16(_dafny.UnicodeSeqOfUtf8Bytes("\\f")) }; return (func () _dafny.Sequence { if ((str).Select((start).Uint32()).(uint16)) == (uint16(10)) { return Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF16(_dafny.UnicodeSeqOfUtf8Bytes("\\n")) }; return (func () _dafny.Sequence { if ((str).Select((start).Uint32()).(uint16)) == (uint16(13)) { return Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF16(_dafny.UnicodeSeqOfUtf8Bytes("\\r")) }; return (func () _dafny.Sequence { if ((str).Select((start).Uint32()).(uint16)) == (uint16(9)) { return Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF16(_dafny.UnicodeSeqOfUtf8Bytes("\\t")) }; return func (_pat_let1_0 uint16) _dafny.Sequence {
      return func (_307_c uint16) _dafny.Sequence {
        return (func () _dafny.Sequence { if (_307_c) < (uint16(31)) { return _dafny.Companion_Sequence_.Concatenate(Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF16(_dafny.UnicodeSeqOfUtf8Bytes("\\u")), Companion_Default___.EscapeUnicode(_307_c)) }; return _dafny.SeqOf((_pat_let_tv0).Select((_pat_let_tv1).Uint32()).(uint16)) })() 
      }(_pat_let1_0)
    }((str).Select((start).Uint32()).(uint16)) })()  })()  })()  })()  })()  })()  })() )
    var _in61 _dafny.Sequence = str
    _ = _in61
    var _in62 _dafny.Int = (start).Plus(_dafny.One)
    _ = _in62
    str = _in61
    start = _in62
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) EscapeToUTF8(str _dafny.Sequence, start _dafny.Int) Std_Wrappers.Result {
  var _308_valueOrError0 Std_Wrappers.Result = (Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ToUTF16Checked(str)).ToResult(Std_JSON_Errors.Companion_SerializationError_.Create_InvalidUnicode_())
  _ = _308_valueOrError0
  if ((_308_valueOrError0).IsFailure()) {
    return (_308_valueOrError0).PropagateFailure()
  } else {
    var _309_utf16 _dafny.Sequence = (_308_valueOrError0).Extract().(_dafny.Sequence)
    _ = _309_utf16
    var _310_escaped _dafny.Sequence = Companion_Default___.Escape(_309_utf16, _dafny.Zero)
    _ = _310_escaped
    var _311_valueOrError1 Std_Wrappers.Result = (Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.FromUTF16Checked(_310_escaped)).ToResult(Std_JSON_Errors.Companion_SerializationError_.Create_InvalidUnicode_())
    _ = _311_valueOrError1
    if ((_311_valueOrError1).IsFailure()) {
      return (_311_valueOrError1).PropagateFailure()
    } else {
      var _312_utf32 _dafny.Sequence = (_311_valueOrError1).Extract().(_dafny.Sequence)
      _ = _312_utf32
      return (Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ToUTF8Checked(_312_utf32)).ToResult(Std_JSON_Errors.Companion_SerializationError_.Create_InvalidUnicode_())
    }
  }
}
func (_static *CompanionStruct_Default___) String(str _dafny.Sequence) Std_Wrappers.Result {
  var _313_valueOrError0 Std_Wrappers.Result = Companion_Default___.EscapeToUTF8(str, _dafny.Zero)
  _ = _313_valueOrError0
  if ((_313_valueOrError0).IsFailure()) {
    return (_313_valueOrError0).PropagateFailure()
  } else {
    var _314_inBytes _dafny.Sequence = (_313_valueOrError0).Extract().(_dafny.Sequence)
    _ = _314_inBytes
    return Std_Wrappers.Companion_Result_.Create_Success_(_dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF8(_dafny.UnicodeSeqOfUtf8Bytes("\"")), _314_inBytes), Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF8(_dafny.UnicodeSeqOfUtf8Bytes("\""))))
  }
}
func (_static *CompanionStruct_Default___) IntToBytes(n _dafny.Int) _dafny.Sequence {
  var _315_s _dafny.Sequence = Std_Strings.Companion_Default___.OfInt(n)
  _ = _315_s
  return Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF8(_315_s)
}
func (_static *CompanionStruct_Default___) Number(dec Std_JSON_Values.Decimal) Std_Wrappers.Result {
  return Std_Wrappers.Companion_Result_.Create_Success_(_dafny.Companion_Sequence_.Concatenate(Companion_Default___.IntToBytes((dec).Dtor_n()), (func () _dafny.Sequence { if ((dec).Dtor_e10()).Sign() == 0 { return _dafny.SeqOf() }; return _dafny.Companion_Sequence_.Concatenate(Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF8(_dafny.UnicodeSeqOfUtf8Bytes("e")), Companion_Default___.IntToBytes((dec).Dtor_e10())) })() ))
}
func (_static *CompanionStruct_Default___) KeyValue(kv _dafny.Tuple) Std_Wrappers.Result {
  var _316_valueOrError0 Std_Wrappers.Result = Companion_Default___.String((*((kv)).IndexInt(0)).(_dafny.Sequence))
  _ = _316_valueOrError0
  if ((_316_valueOrError0).IsFailure()) {
    return (_316_valueOrError0).PropagateFailure()
  } else {
    var _317_key _dafny.Sequence = (_316_valueOrError0).Extract().(_dafny.Sequence)
    _ = _317_key
    var _318_valueOrError1 Std_Wrappers.Result = Companion_Default___.JSON((*((kv)).IndexInt(1)).(Std_JSON_Values.JSON))
    _ = _318_valueOrError1
    if ((_318_valueOrError1).IsFailure()) {
      return (_318_valueOrError1).PropagateFailure()
    } else {
      var _319_value _dafny.Sequence = (_318_valueOrError1).Extract().(_dafny.Sequence)
      _ = _319_value
      return Std_Wrappers.Companion_Result_.Create_Success_(_dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(_317_key, Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF8(_dafny.UnicodeSeqOfUtf8Bytes(":"))), _319_value))
    }
  }
}
func (_static *CompanionStruct_Default___) Join(sep _dafny.Sequence, items _dafny.Sequence) Std_Wrappers.Result {
  if ((_dafny.IntOfUint32((items).Cardinality())).Sign() == 0) {
    return Std_Wrappers.Companion_Result_.Create_Success_(_dafny.SeqOf())
  } else {
    var _320_valueOrError0 Std_Wrappers.Result = (items).Select(0).(Std_Wrappers.Result)
    _ = _320_valueOrError0
    if ((_320_valueOrError0).IsFailure()) {
      return (_320_valueOrError0).PropagateFailure()
    } else {
      var _321_first _dafny.Sequence = (_320_valueOrError0).Extract().(_dafny.Sequence)
      _ = _321_first
      if ((_dafny.IntOfUint32((items).Cardinality())).Cmp(_dafny.One) == 0) {
        return Std_Wrappers.Companion_Result_.Create_Success_(_321_first)
      } else {
        var _322_valueOrError1 Std_Wrappers.Result = Companion_Default___.Join(sep, (items).Drop(1))
        _ = _322_valueOrError1
        if ((_322_valueOrError1).IsFailure()) {
          return (_322_valueOrError1).PropagateFailure()
        } else {
          var _323_rest _dafny.Sequence = (_322_valueOrError1).Extract().(_dafny.Sequence)
          _ = _323_rest
          return Std_Wrappers.Companion_Result_.Create_Success_(_dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(_321_first, sep), _323_rest))
        }
      }
    }
  }
}
func (_static *CompanionStruct_Default___) Object(obj _dafny.Sequence) Std_Wrappers.Result {
  var _324_valueOrError0 Std_Wrappers.Result = Companion_Default___.Join(Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF8(_dafny.UnicodeSeqOfUtf8Bytes(",")), _dafny.SeqCreate((_dafny.IntOfUint32((obj).Cardinality())).Uint32(), func (coer24 func (_dafny.Int) Std_Wrappers.Result) func (_dafny.Int) interface{} {
    return func (arg26 _dafny.Int) interface{} {
      return coer24(arg26)
    }
  }((func (_325_obj _dafny.Sequence) func (_dafny.Int) Std_Wrappers.Result {
    return func (_326_i _dafny.Int) Std_Wrappers.Result {
      return Companion_Default___.KeyValue((_325_obj).Select((_326_i).Uint32()).(_dafny.Tuple))
    }
  })(obj))))
  _ = _324_valueOrError0
  if ((_324_valueOrError0).IsFailure()) {
    return (_324_valueOrError0).PropagateFailure()
  } else {
    var _327_middle _dafny.Sequence = (_324_valueOrError0).Extract().(_dafny.Sequence)
    _ = _327_middle
    return Std_Wrappers.Companion_Result_.Create_Success_(_dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF8(_dafny.UnicodeSeqOfUtf8Bytes("{")), _327_middle), Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF8(_dafny.UnicodeSeqOfUtf8Bytes("}"))))
  }
}
func (_static *CompanionStruct_Default___) Array(arr _dafny.Sequence) Std_Wrappers.Result {
  var _328_valueOrError0 Std_Wrappers.Result = Companion_Default___.Join(Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF8(_dafny.UnicodeSeqOfUtf8Bytes(",")), _dafny.SeqCreate((_dafny.IntOfUint32((arr).Cardinality())).Uint32(), func (coer25 func (_dafny.Int) Std_Wrappers.Result) func (_dafny.Int) interface{} {
    return func (arg27 _dafny.Int) interface{} {
      return coer25(arg27)
    }
  }((func (_329_arr _dafny.Sequence) func (_dafny.Int) Std_Wrappers.Result {
    return func (_330_i _dafny.Int) Std_Wrappers.Result {
      return Companion_Default___.JSON((_329_arr).Select((_330_i).Uint32()).(Std_JSON_Values.JSON))
    }
  })(arr))))
  _ = _328_valueOrError0
  if ((_328_valueOrError0).IsFailure()) {
    return (_328_valueOrError0).PropagateFailure()
  } else {
    var _331_middle _dafny.Sequence = (_328_valueOrError0).Extract().(_dafny.Sequence)
    _ = _331_middle
    return Std_Wrappers.Companion_Result_.Create_Success_(_dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF8(_dafny.UnicodeSeqOfUtf8Bytes("[")), _331_middle), Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF8(_dafny.UnicodeSeqOfUtf8Bytes("]"))))
  }
}
func (_static *CompanionStruct_Default___) JSON(js Std_JSON_Values.JSON) Std_Wrappers.Result {
  var _source12 Std_JSON_Values.JSON = js
  _ = _source12
  if (_source12.Is_Null()) {
    return Std_Wrappers.Companion_Result_.Create_Success_(Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF8(_dafny.UnicodeSeqOfUtf8Bytes("null")))
  } else if (_source12.Is_Bool()) {
    var _332___mcc_h0 bool = _source12.Get_().(Std_JSON_Values.JSON_Bool).B
    _ = _332___mcc_h0
    var _333_b bool = _332___mcc_h0
    _ = _333_b
    return Std_Wrappers.Companion_Result_.Create_Success_((func () _dafny.Sequence { if _333_b { return Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF8(_dafny.UnicodeSeqOfUtf8Bytes("true")) }; return Std_Unicode_UnicodeStringsWithUnicodeChar.Companion_Default___.ASCIIToUTF8(_dafny.UnicodeSeqOfUtf8Bytes("false")) })() )
  } else if (_source12.Is_String()) {
    var _334___mcc_h1 _dafny.Sequence = _source12.Get_().(Std_JSON_Values.JSON_String).Str
    _ = _334___mcc_h1
    var _335_str _dafny.Sequence = _334___mcc_h1
    _ = _335_str
    return Companion_Default___.String(_335_str)
  } else if (_source12.Is_Number()) {
    var _336___mcc_h2 Std_JSON_Values.Decimal = _source12.Get_().(Std_JSON_Values.JSON_Number).Num
    _ = _336___mcc_h2
    var _337_dec Std_JSON_Values.Decimal = _336___mcc_h2
    _ = _337_dec
    return Companion_Default___.Number(_337_dec)
  } else if (_source12.Is_Object()) {
    var _338___mcc_h3 _dafny.Sequence = _source12.Get_().(Std_JSON_Values.JSON_Object).Obj
    _ = _338___mcc_h3
    var _339_obj _dafny.Sequence = _338___mcc_h3
    _ = _339_obj
    return Companion_Default___.Object(_339_obj)
  } else {
    var _340___mcc_h4 _dafny.Sequence = _source12.Get_().(Std_JSON_Values.JSON_Array).Arr
    _ = _340___mcc_h4
    var _341_arr _dafny.Sequence = _340___mcc_h4
    _ = _341_arr
    return Companion_Default___.Array(_341_arr)
  }
}
// End of class Default__
