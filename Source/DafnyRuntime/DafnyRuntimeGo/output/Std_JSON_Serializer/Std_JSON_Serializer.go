// Package Std_JSON_Serializer
// Dafny module Std_JSON_Serializer compiled into Go

package Std_JSON_Serializer

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
  return "Std_JSON_Serializer.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) Bool(b bool) Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes((func () _dafny.Sequence { if b { return Std_JSON_Grammar.Companion_Default___.TRUE() }; return Std_JSON_Grammar.Companion_Default___.FALSE() })() )
}
func (_static *CompanionStruct_Default___) CheckLength(s _dafny.Sequence, err Std_JSON_Errors.SerializationError) Std_Wrappers.Outcome {
  return Std_Wrappers.Companion_Outcome_.Need((_dafny.IntOfUint32((s).Cardinality())).Cmp(Std_BoundedInts.Companion_Default___.TWO__TO__THE__32()) < 0, err)
}
func (_static *CompanionStruct_Default___) String(str _dafny.Sequence) Std_Wrappers.Result {
  var _416_valueOrError0 Std_Wrappers.Result = Std_JSON_Spec.Companion_Default___.EscapeToUTF8(str, _dafny.Zero)
  _ = _416_valueOrError0
  if ((_416_valueOrError0).IsFailure()) {
    return (_416_valueOrError0).PropagateFailure()
  } else {
    var _417_bs _dafny.Sequence = (_416_valueOrError0).Extract().(_dafny.Sequence)
    _ = _417_bs
    var _418_o Std_Wrappers.Outcome = Companion_Default___.CheckLength(_417_bs, Std_JSON_Errors.Companion_SerializationError_.Create_StringTooLong_(str))
    _ = _418_o
    if ((_418_o).Is_Pass()) {
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Jstring_.Create_JString_(Std_JSON_Grammar.Companion_Default___.DOUBLEQUOTE(), Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_417_bs), Std_JSON_Grammar.Companion_Default___.DOUBLEQUOTE()))
    } else {
      return Std_Wrappers.Companion_Result_.Create_Failure_((_418_o).Dtor_error().(Std_JSON_Errors.SerializationError))
    }
  }
}
func (_static *CompanionStruct_Default___) Sign(n _dafny.Int) Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes((func () _dafny.Sequence { if (n).Sign() == -1 { return _dafny.SeqOf(uint8(_dafny.CodePoint('-'))) }; return _dafny.SeqOf() })() )
}
func (_static *CompanionStruct_Default___) Int_k(n _dafny.Int) _dafny.Sequence {
  return Std_JSON_ByteStrConversion.Companion_Default___.OfInt(n, Companion_Default___.MINUS())
}
func (_static *CompanionStruct_Default___) Int(n _dafny.Int) Std_Wrappers.Result {
  var _419_bs _dafny.Sequence = Companion_Default___.Int_k(n)
  _ = _419_bs
  var _420_o Std_Wrappers.Outcome = Companion_Default___.CheckLength(_419_bs, Std_JSON_Errors.Companion_SerializationError_.Create_IntTooLarge_(n))
  _ = _420_o
  if ((_420_o).Is_Pass()) {
    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_419_bs))
  } else {
    return Std_Wrappers.Companion_Result_.Create_Failure_((_420_o).Dtor_error().(Std_JSON_Errors.SerializationError))
  }
}
func (_static *CompanionStruct_Default___) Number(dec Std_JSON_Values.Decimal) Std_Wrappers.Result {
  var _pat_let_tv2 = dec
  _ = _pat_let_tv2
  var _pat_let_tv3 = dec
  _ = _pat_let_tv3
  var _421_minus Std_JSON_Utils_Views_Core.View__ = Companion_Default___.Sign((dec).Dtor_n())
  _ = _421_minus
  var _422_valueOrError0 Std_Wrappers.Result = Companion_Default___.Int(Std_Math.Companion_Default___.Abs((dec).Dtor_n()))
  _ = _422_valueOrError0
  if ((_422_valueOrError0).IsFailure()) {
    return (_422_valueOrError0).PropagateFailure()
  } else {
    var _423_num Std_JSON_Utils_Views_Core.View__ = (_422_valueOrError0).Extract().(Std_JSON_Utils_Views_Core.View__)
    _ = _423_num
    var _424_frac Std_JSON_Grammar.Maybe = Std_JSON_Grammar.Companion_Maybe_.Create_Empty_()
    _ = _424_frac
    var _425_valueOrError1 Std_Wrappers.Result = (func () Std_Wrappers.Result { if ((dec).Dtor_e10()).Sign() == 0 { return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Maybe_.Create_Empty_()) }; return func (_pat_let2_0 Std_JSON_Utils_Views_Core.View__) Std_Wrappers.Result {
      return func (_426_e Std_JSON_Utils_Views_Core.View__) Std_Wrappers.Result {
        return func (_pat_let3_0 Std_JSON_Utils_Views_Core.View__) Std_Wrappers.Result {
          return func (_427_sign Std_JSON_Utils_Views_Core.View__) Std_Wrappers.Result {
            return func (_pat_let4_0 Std_Wrappers.Result) Std_Wrappers.Result {
              return func (_428_valueOrError2 Std_Wrappers.Result) Std_Wrappers.Result {
                return (func () Std_Wrappers.Result { if (_428_valueOrError2).IsFailure() { return (_428_valueOrError2).PropagateFailure() }; return func (_pat_let5_0 Std_JSON_Utils_Views_Core.View__) Std_Wrappers.Result {
                  return func (_429_num Std_JSON_Utils_Views_Core.View__) Std_Wrappers.Result {
                    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Maybe_.Create_NonEmpty_(Std_JSON_Grammar.Companion_Jexp_.Create_JExp_(_426_e, _427_sign, _429_num)))
                  }(_pat_let5_0)
                }((_428_valueOrError2).Extract().(Std_JSON_Utils_Views_Core.View__)) })() 
              }(_pat_let4_0)
            }(Companion_Default___.Int(Std_Math.Companion_Default___.Abs((_pat_let_tv3).Dtor_e10())))
          }(_pat_let3_0)
        }(Companion_Default___.Sign((_pat_let_tv2).Dtor_e10()))
      }(_pat_let2_0)
    }(Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf(uint8(_dafny.CodePoint('e'))))) })() 
    _ = _425_valueOrError1
    if ((_425_valueOrError1).IsFailure()) {
      return (_425_valueOrError1).PropagateFailure()
    } else {
      var _430_exp Std_JSON_Grammar.Maybe = (_425_valueOrError1).Extract().(Std_JSON_Grammar.Maybe)
      _ = _430_exp
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Jnumber_.Create_JNumber_(_421_minus, _423_num, Std_JSON_Grammar.Companion_Maybe_.Create_Empty_(), _430_exp))
    }
  }
}
func (_static *CompanionStruct_Default___) MkStructural(v interface{}) Std_JSON_Grammar.Structural {
  return Std_JSON_Grammar.Companion_Structural_.Create_Structural_(Std_JSON_Grammar.Companion_Default___.EMPTY(), v, Std_JSON_Grammar.Companion_Default___.EMPTY())
}
func (_static *CompanionStruct_Default___) KeyValue(kv _dafny.Tuple) Std_Wrappers.Result {
  var _431_valueOrError0 Std_Wrappers.Result = Companion_Default___.String((*((kv)).IndexInt(0)).(_dafny.Sequence))
  _ = _431_valueOrError0
  if ((_431_valueOrError0).IsFailure()) {
    return (_431_valueOrError0).PropagateFailure()
  } else {
    var _432_k Std_JSON_Grammar.Jstring = (_431_valueOrError0).Extract().(Std_JSON_Grammar.Jstring)
    _ = _432_k
    var _433_valueOrError1 Std_Wrappers.Result = Companion_Default___.Value((*((kv)).IndexInt(1)).(Std_JSON_Values.JSON))
    _ = _433_valueOrError1
    if ((_433_valueOrError1).IsFailure()) {
      return (_433_valueOrError1).PropagateFailure()
    } else {
      var _434_v Std_JSON_Grammar.Value = (_433_valueOrError1).Extract().(Std_JSON_Grammar.Value)
      _ = _434_v
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_JKeyValue_.Create_KeyValue_(_432_k, Companion_Default___.COLON(), _434_v))
    }
  }
}
func (_static *CompanionStruct_Default___) MkSuffixedSequence(ds _dafny.Sequence, suffix Std_JSON_Grammar.Structural, start _dafny.Int) _dafny.Sequence {
  var _435___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _435___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((start).Cmp(_dafny.IntOfUint32((ds).Cardinality())) >= 0) {
    return _dafny.Companion_Sequence_.Concatenate(_435___accumulator, _dafny.SeqOf())
  } else if ((start).Cmp((_dafny.IntOfUint32((ds).Cardinality())).Minus(_dafny.One)) == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_435___accumulator, _dafny.SeqOf(Std_JSON_Grammar.Companion_Suffixed_.Create_Suffixed_((ds).Select((start).Uint32()).(interface{}), Std_JSON_Grammar.Companion_Maybe_.Create_Empty_())))
  } else {
    _435___accumulator = _dafny.Companion_Sequence_.Concatenate(_435___accumulator, _dafny.SeqOf(Std_JSON_Grammar.Companion_Suffixed_.Create_Suffixed_((ds).Select((start).Uint32()).(interface{}), Std_JSON_Grammar.Companion_Maybe_.Create_NonEmpty_(suffix))))
    var _in78 _dafny.Sequence = ds
    _ = _in78
    var _in79 Std_JSON_Grammar.Structural = suffix
    _ = _in79
    var _in80 _dafny.Int = (start).Plus(_dafny.One)
    _ = _in80
    ds = _in78
    suffix = _in79
    start = _in80
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) Object(obj _dafny.Sequence) Std_Wrappers.Result {
  var _436_valueOrError0 Std_Wrappers.Result = Std_Collections_Seq.Companion_Default___.MapWithResult(func (coer32 func (_dafny.Tuple) Std_Wrappers.Result) func (interface{}) Std_Wrappers.Result {
    return func (arg34 interface{}) Std_Wrappers.Result {
      return coer32(arg34.(_dafny.Tuple))
    }
  }((func (_437_obj _dafny.Sequence) func (_dafny.Tuple) Std_Wrappers.Result {
    return func (_438_v _dafny.Tuple) Std_Wrappers.Result {
      return Companion_Default___.KeyValue(_438_v)
    }
  })(obj)), obj)
  _ = _436_valueOrError0
  if ((_436_valueOrError0).IsFailure()) {
    return (_436_valueOrError0).PropagateFailure()
  } else {
    var _439_items _dafny.Sequence = (_436_valueOrError0).Extract().(_dafny.Sequence)
    _ = _439_items
    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Bracketed_.Create_Bracketed_(Companion_Default___.MkStructural(Std_JSON_Grammar.Companion_Default___.LBRACE()), Companion_Default___.MkSuffixedSequence(_439_items, Companion_Default___.COMMA(), _dafny.Zero), Companion_Default___.MkStructural(Std_JSON_Grammar.Companion_Default___.RBRACE())))
  }
}
func (_static *CompanionStruct_Default___) Array(arr _dafny.Sequence) Std_Wrappers.Result {
  var _440_valueOrError0 Std_Wrappers.Result = Std_Collections_Seq.Companion_Default___.MapWithResult(func (coer33 func (Std_JSON_Values.JSON) Std_Wrappers.Result) func (interface{}) Std_Wrappers.Result {
    return func (arg35 interface{}) Std_Wrappers.Result {
      return coer33(arg35.(Std_JSON_Values.JSON))
    }
  }((func (_441_arr _dafny.Sequence) func (Std_JSON_Values.JSON) Std_Wrappers.Result {
    return func (_442_v Std_JSON_Values.JSON) Std_Wrappers.Result {
      return Companion_Default___.Value(_442_v)
    }
  })(arr)), arr)
  _ = _440_valueOrError0
  if ((_440_valueOrError0).IsFailure()) {
    return (_440_valueOrError0).PropagateFailure()
  } else {
    var _443_items _dafny.Sequence = (_440_valueOrError0).Extract().(_dafny.Sequence)
    _ = _443_items
    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Bracketed_.Create_Bracketed_(Companion_Default___.MkStructural(Std_JSON_Grammar.Companion_Default___.LBRACKET()), Companion_Default___.MkSuffixedSequence(_443_items, Companion_Default___.COMMA(), _dafny.Zero), Companion_Default___.MkStructural(Std_JSON_Grammar.Companion_Default___.RBRACKET())))
  }
}
func (_static *CompanionStruct_Default___) Value(js Std_JSON_Values.JSON) Std_Wrappers.Result {
  var _source16 Std_JSON_Values.JSON = js
  _ = _source16
  if (_source16.Is_Null()) {
    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Value_.Create_Null_(Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(Std_JSON_Grammar.Companion_Default___.NULL())))
  } else if (_source16.Is_Bool()) {
    var _444___mcc_h0 bool = _source16.Get_().(Std_JSON_Values.JSON_Bool).B
    _ = _444___mcc_h0
    var _445_b bool = _444___mcc_h0
    _ = _445_b
    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Value_.Create_Bool_(Companion_Default___.Bool(_445_b)))
  } else if (_source16.Is_String()) {
    var _446___mcc_h1 _dafny.Sequence = _source16.Get_().(Std_JSON_Values.JSON_String).Str
    _ = _446___mcc_h1
    var _447_str _dafny.Sequence = _446___mcc_h1
    _ = _447_str
    var _448_valueOrError0 Std_Wrappers.Result = Companion_Default___.String(_447_str)
    _ = _448_valueOrError0
    if ((_448_valueOrError0).IsFailure()) {
      return (_448_valueOrError0).PropagateFailure()
    } else {
      var _449_s Std_JSON_Grammar.Jstring = (_448_valueOrError0).Extract().(Std_JSON_Grammar.Jstring)
      _ = _449_s
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Value_.Create_String_(_449_s))
    }
  } else if (_source16.Is_Number()) {
    var _450___mcc_h2 Std_JSON_Values.Decimal = _source16.Get_().(Std_JSON_Values.JSON_Number).Num
    _ = _450___mcc_h2
    var _451_dec Std_JSON_Values.Decimal = _450___mcc_h2
    _ = _451_dec
    var _452_valueOrError1 Std_Wrappers.Result = Companion_Default___.Number(_451_dec)
    _ = _452_valueOrError1
    if ((_452_valueOrError1).IsFailure()) {
      return (_452_valueOrError1).PropagateFailure()
    } else {
      var _453_n Std_JSON_Grammar.Jnumber = (_452_valueOrError1).Extract().(Std_JSON_Grammar.Jnumber)
      _ = _453_n
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Value_.Create_Number_(_453_n))
    }
  } else if (_source16.Is_Object()) {
    var _454___mcc_h3 _dafny.Sequence = _source16.Get_().(Std_JSON_Values.JSON_Object).Obj
    _ = _454___mcc_h3
    var _455_obj _dafny.Sequence = _454___mcc_h3
    _ = _455_obj
    var _456_valueOrError2 Std_Wrappers.Result = Companion_Default___.Object(_455_obj)
    _ = _456_valueOrError2
    if ((_456_valueOrError2).IsFailure()) {
      return (_456_valueOrError2).PropagateFailure()
    } else {
      var _457_o Std_JSON_Grammar.Bracketed = (_456_valueOrError2).Extract().(Std_JSON_Grammar.Bracketed)
      _ = _457_o
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Value_.Create_Object_(_457_o))
    }
  } else {
    var _458___mcc_h4 _dafny.Sequence = _source16.Get_().(Std_JSON_Values.JSON_Array).Arr
    _ = _458___mcc_h4
    var _459_arr _dafny.Sequence = _458___mcc_h4
    _ = _459_arr
    var _460_valueOrError3 Std_Wrappers.Result = Companion_Default___.Array(_459_arr)
    _ = _460_valueOrError3
    if ((_460_valueOrError3).IsFailure()) {
      return (_460_valueOrError3).PropagateFailure()
    } else {
      var _461_a Std_JSON_Grammar.Bracketed = (_460_valueOrError3).Extract().(Std_JSON_Grammar.Bracketed)
      _ = _461_a
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Value_.Create_Array_(_461_a))
    }
  }
}
func (_static *CompanionStruct_Default___) JSON(js Std_JSON_Values.JSON) Std_Wrappers.Result {
  var _462_valueOrError0 Std_Wrappers.Result = Companion_Default___.Value(js)
  _ = _462_valueOrError0
  if ((_462_valueOrError0).IsFailure()) {
    return (_462_valueOrError0).PropagateFailure()
  } else {
    var _463_val Std_JSON_Grammar.Value = (_462_valueOrError0).Extract().(Std_JSON_Grammar.Value)
    _ = _463_val
    return Std_Wrappers.Companion_Result_.Create_Success_(Companion_Default___.MkStructural(_463_val))
  }
}
func (_static *CompanionStruct_Default___) DIGITS() _dafny.Sequence {
  return Std_JSON_ByteStrConversion.Companion_Default___.Chars()
}
func (_static *CompanionStruct_Default___) MINUS() uint8 {
  return uint8(_dafny.CodePoint('-'))
}
func (_static *CompanionStruct_Default___) COLON() Std_JSON_Grammar.Structural {
  return Companion_Default___.MkStructural(Std_JSON_Grammar.Companion_Default___.COLON())
}
func (_static *CompanionStruct_Default___) COMMA() Std_JSON_Grammar.Structural {
  return Companion_Default___.MkStructural(Std_JSON_Grammar.Companion_Default___.COMMA())
}
// End of class Default__

// Definition of class Bytes32
type Bytes32 struct {
}

func New_Bytes32_() *Bytes32 {
  _this := Bytes32{}

  return &_this
}

type CompanionStruct_Bytes32_ struct {
}
var Companion_Bytes32_ = CompanionStruct_Bytes32_ {
}

func (*Bytes32) String() string {
  return "Std_JSON_Serializer.Bytes32"
}
// End of class Bytes32

func Type_Bytes32_() _dafny.TypeDescriptor {
  return type_Bytes32_{}
}

type type_Bytes32_ struct {
}

func (_this type_Bytes32_) Default() interface{} {
  return _dafny.EmptySeq
}

func (_this type_Bytes32_) String() string {
  return "Std_JSON_Serializer.Bytes32"
}

// Definition of class String32
type String32 struct {
}

func New_String32_() *String32 {
  _this := String32{}

  return &_this
}

type CompanionStruct_String32_ struct {
}
var Companion_String32_ = CompanionStruct_String32_ {
}

func (*String32) String() string {
  return "Std_JSON_Serializer.String32"
}
// End of class String32

func Type_String32_() _dafny.TypeDescriptor {
  return type_String32_{}
}

type type_String32_ struct {
}

func (_this type_String32_) Default() interface{} {
  return _dafny.EmptySeq
}

func (_this type_String32_) String() string {
  return "Std_JSON_Serializer.String32"
}
