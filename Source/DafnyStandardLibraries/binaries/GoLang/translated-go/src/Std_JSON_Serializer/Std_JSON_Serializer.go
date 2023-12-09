// Package Std_JSON_Serializer
// Dafny module Std_JSON_Serializer compiled into Go

package Std_JSON_Serializer

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
  var _408_valueOrError0 Std_Wrappers.Result = Std_JSON_Spec.Companion_Default___.EscapeToUTF8(str, _dafny.Zero)
  _ = _408_valueOrError0
  if ((_408_valueOrError0).IsFailure()) {
    return (_408_valueOrError0).PropagateFailure()
  } else {
    var _409_bs _dafny.Sequence = (_408_valueOrError0).Extract().(_dafny.Sequence)
    _ = _409_bs
    var _410_o Std_Wrappers.Outcome = Companion_Default___.CheckLength(_409_bs, Std_JSON_Errors.Companion_SerializationError_.Create_StringTooLong_(str))
    _ = _410_o
    if ((_410_o).Is_Pass()) {
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Jstring_.Create_JString_(Std_JSON_Grammar.Companion_Default___.DOUBLEQUOTE(), Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_409_bs), Std_JSON_Grammar.Companion_Default___.DOUBLEQUOTE()))
    } else {
      return Std_Wrappers.Companion_Result_.Create_Failure_((_410_o).Dtor_error().(Std_JSON_Errors.SerializationError))
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
  var _411_bs _dafny.Sequence = Companion_Default___.Int_k(n)
  _ = _411_bs
  var _412_o Std_Wrappers.Outcome = Companion_Default___.CheckLength(_411_bs, Std_JSON_Errors.Companion_SerializationError_.Create_IntTooLarge_(n))
  _ = _412_o
  if ((_412_o).Is_Pass()) {
    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_411_bs))
  } else {
    return Std_Wrappers.Companion_Result_.Create_Failure_((_412_o).Dtor_error().(Std_JSON_Errors.SerializationError))
  }
}
func (_static *CompanionStruct_Default___) Number(dec Std_JSON_Values.Decimal) Std_Wrappers.Result {
  var _pat_let_tv2 = dec
  _ = _pat_let_tv2
  var _pat_let_tv3 = dec
  _ = _pat_let_tv3
  var _413_minus Std_JSON_Utils_Views_Core.View__ = Companion_Default___.Sign((dec).Dtor_n())
  _ = _413_minus
  var _414_valueOrError0 Std_Wrappers.Result = Companion_Default___.Int(Std_Math.Companion_Default___.Abs((dec).Dtor_n()))
  _ = _414_valueOrError0
  if ((_414_valueOrError0).IsFailure()) {
    return (_414_valueOrError0).PropagateFailure()
  } else {
    var _415_num Std_JSON_Utils_Views_Core.View__ = (_414_valueOrError0).Extract().(Std_JSON_Utils_Views_Core.View__)
    _ = _415_num
    var _416_frac Std_JSON_Grammar.Maybe = Std_JSON_Grammar.Companion_Maybe_.Create_Empty_()
    _ = _416_frac
    var _417_valueOrError1 Std_Wrappers.Result = (func () Std_Wrappers.Result { if ((dec).Dtor_e10()).Sign() == 0 { return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Maybe_.Create_Empty_()) }; return func (_pat_let2_0 Std_JSON_Utils_Views_Core.View__) Std_Wrappers.Result {
      return func (_418_e Std_JSON_Utils_Views_Core.View__) Std_Wrappers.Result {
        return func (_pat_let3_0 Std_JSON_Utils_Views_Core.View__) Std_Wrappers.Result {
          return func (_419_sign Std_JSON_Utils_Views_Core.View__) Std_Wrappers.Result {
            return func (_pat_let4_0 Std_Wrappers.Result) Std_Wrappers.Result {
              return func (_420_valueOrError2 Std_Wrappers.Result) Std_Wrappers.Result {
                return (func () Std_Wrappers.Result { if (_420_valueOrError2).IsFailure() { return (_420_valueOrError2).PropagateFailure() }; return func (_pat_let5_0 Std_JSON_Utils_Views_Core.View__) Std_Wrappers.Result {
                  return func (_421_num Std_JSON_Utils_Views_Core.View__) Std_Wrappers.Result {
                    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Maybe_.Create_NonEmpty_(Std_JSON_Grammar.Companion_Jexp_.Create_JExp_(_418_e, _419_sign, _421_num)))
                  }(_pat_let5_0)
                }((_420_valueOrError2).Extract().(Std_JSON_Utils_Views_Core.View__)) })() 
              }(_pat_let4_0)
            }(Companion_Default___.Int(Std_Math.Companion_Default___.Abs((_pat_let_tv3).Dtor_e10())))
          }(_pat_let3_0)
        }(Companion_Default___.Sign((_pat_let_tv2).Dtor_e10()))
      }(_pat_let2_0)
    }(Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf(uint8(_dafny.CodePoint('e'))))) })() 
    _ = _417_valueOrError1
    if ((_417_valueOrError1).IsFailure()) {
      return (_417_valueOrError1).PropagateFailure()
    } else {
      var _422_exp Std_JSON_Grammar.Maybe = (_417_valueOrError1).Extract().(Std_JSON_Grammar.Maybe)
      _ = _422_exp
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Jnumber_.Create_JNumber_(_413_minus, _415_num, Std_JSON_Grammar.Companion_Maybe_.Create_Empty_(), _422_exp))
    }
  }
}
func (_static *CompanionStruct_Default___) MkStructural(v interface{}) Std_JSON_Grammar.Structural {
  return Std_JSON_Grammar.Companion_Structural_.Create_Structural_(Std_JSON_Grammar.Companion_Default___.EMPTY(), v, Std_JSON_Grammar.Companion_Default___.EMPTY())
}
func (_static *CompanionStruct_Default___) KeyValue(kv _dafny.Tuple) Std_Wrappers.Result {
  var _423_valueOrError0 Std_Wrappers.Result = Companion_Default___.String((*((kv)).IndexInt(0)).(_dafny.Sequence))
  _ = _423_valueOrError0
  if ((_423_valueOrError0).IsFailure()) {
    return (_423_valueOrError0).PropagateFailure()
  } else {
    var _424_k Std_JSON_Grammar.Jstring = (_423_valueOrError0).Extract().(Std_JSON_Grammar.Jstring)
    _ = _424_k
    var _425_valueOrError1 Std_Wrappers.Result = Companion_Default___.Value((*((kv)).IndexInt(1)).(Std_JSON_Values.JSON))
    _ = _425_valueOrError1
    if ((_425_valueOrError1).IsFailure()) {
      return (_425_valueOrError1).PropagateFailure()
    } else {
      var _426_v Std_JSON_Grammar.Value = (_425_valueOrError1).Extract().(Std_JSON_Grammar.Value)
      _ = _426_v
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_JKeyValue_.Create_KeyValue_(_424_k, Companion_Default___.COLON(), _426_v))
    }
  }
}
func (_static *CompanionStruct_Default___) MkSuffixedSequence(ds _dafny.Sequence, suffix Std_JSON_Grammar.Structural, start _dafny.Int) _dafny.Sequence {
  var _427___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _427___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((start).Cmp(_dafny.IntOfUint32((ds).Cardinality())) >= 0) {
    return _dafny.Companion_Sequence_.Concatenate(_427___accumulator, _dafny.SeqOf())
  } else if ((start).Cmp((_dafny.IntOfUint32((ds).Cardinality())).Minus(_dafny.One)) == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_427___accumulator, _dafny.SeqOf(Std_JSON_Grammar.Companion_Suffixed_.Create_Suffixed_((ds).Select((start).Uint32()).(interface{}), Std_JSON_Grammar.Companion_Maybe_.Create_Empty_())))
  } else {
    _427___accumulator = _dafny.Companion_Sequence_.Concatenate(_427___accumulator, _dafny.SeqOf(Std_JSON_Grammar.Companion_Suffixed_.Create_Suffixed_((ds).Select((start).Uint32()).(interface{}), Std_JSON_Grammar.Companion_Maybe_.Create_NonEmpty_(suffix))))
    var _in77 _dafny.Sequence = ds
    _ = _in77
    var _in78 Std_JSON_Grammar.Structural = suffix
    _ = _in78
    var _in79 _dafny.Int = (start).Plus(_dafny.One)
    _ = _in79
    ds = _in77
    suffix = _in78
    start = _in79
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) Object(obj _dafny.Sequence) Std_Wrappers.Result {
  var _428_valueOrError0 Std_Wrappers.Result = Std_Collections_Seq.Companion_Default___.MapWithResult(func (coer30 func (_dafny.Tuple) Std_Wrappers.Result) func (interface{}) Std_Wrappers.Result {
    return func (arg32 interface{}) Std_Wrappers.Result {
      return coer30(arg32.(_dafny.Tuple))
    }
  }((func (_429_obj _dafny.Sequence) func (_dafny.Tuple) Std_Wrappers.Result {
    return func (_430_v _dafny.Tuple) Std_Wrappers.Result {
      return Companion_Default___.KeyValue(_430_v)
    }
  })(obj)), obj)
  _ = _428_valueOrError0
  if ((_428_valueOrError0).IsFailure()) {
    return (_428_valueOrError0).PropagateFailure()
  } else {
    var _431_items _dafny.Sequence = (_428_valueOrError0).Extract().(_dafny.Sequence)
    _ = _431_items
    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Bracketed_.Create_Bracketed_(Companion_Default___.MkStructural(Std_JSON_Grammar.Companion_Default___.LBRACE()), Companion_Default___.MkSuffixedSequence(_431_items, Companion_Default___.COMMA(), _dafny.Zero), Companion_Default___.MkStructural(Std_JSON_Grammar.Companion_Default___.RBRACE())))
  }
}
func (_static *CompanionStruct_Default___) Array(arr _dafny.Sequence) Std_Wrappers.Result {
  var _432_valueOrError0 Std_Wrappers.Result = Std_Collections_Seq.Companion_Default___.MapWithResult(func (coer31 func (Std_JSON_Values.JSON) Std_Wrappers.Result) func (interface{}) Std_Wrappers.Result {
    return func (arg33 interface{}) Std_Wrappers.Result {
      return coer31(arg33.(Std_JSON_Values.JSON))
    }
  }((func (_433_arr _dafny.Sequence) func (Std_JSON_Values.JSON) Std_Wrappers.Result {
    return func (_434_v Std_JSON_Values.JSON) Std_Wrappers.Result {
      return Companion_Default___.Value(_434_v)
    }
  })(arr)), arr)
  _ = _432_valueOrError0
  if ((_432_valueOrError0).IsFailure()) {
    return (_432_valueOrError0).PropagateFailure()
  } else {
    var _435_items _dafny.Sequence = (_432_valueOrError0).Extract().(_dafny.Sequence)
    _ = _435_items
    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Bracketed_.Create_Bracketed_(Companion_Default___.MkStructural(Std_JSON_Grammar.Companion_Default___.LBRACKET()), Companion_Default___.MkSuffixedSequence(_435_items, Companion_Default___.COMMA(), _dafny.Zero), Companion_Default___.MkStructural(Std_JSON_Grammar.Companion_Default___.RBRACKET())))
  }
}
func (_static *CompanionStruct_Default___) Value(js Std_JSON_Values.JSON) Std_Wrappers.Result {
  var _source16 Std_JSON_Values.JSON = js
  _ = _source16
  if (_source16.Is_Null()) {
    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Value_.Create_Null_(Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(Std_JSON_Grammar.Companion_Default___.NULL())))
  } else if (_source16.Is_Bool()) {
    var _436___mcc_h0 bool = _source16.Get_().(Std_JSON_Values.JSON_Bool).B
    _ = _436___mcc_h0
    var _437_b bool = _436___mcc_h0
    _ = _437_b
    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Value_.Create_Bool_(Companion_Default___.Bool(_437_b)))
  } else if (_source16.Is_String()) {
    var _438___mcc_h1 _dafny.Sequence = _source16.Get_().(Std_JSON_Values.JSON_String).Str
    _ = _438___mcc_h1
    var _439_str _dafny.Sequence = _438___mcc_h1
    _ = _439_str
    var _440_valueOrError0 Std_Wrappers.Result = Companion_Default___.String(_439_str)
    _ = _440_valueOrError0
    if ((_440_valueOrError0).IsFailure()) {
      return (_440_valueOrError0).PropagateFailure()
    } else {
      var _441_s Std_JSON_Grammar.Jstring = (_440_valueOrError0).Extract().(Std_JSON_Grammar.Jstring)
      _ = _441_s
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Value_.Create_String_(_441_s))
    }
  } else if (_source16.Is_Number()) {
    var _442___mcc_h2 Std_JSON_Values.Decimal = _source16.Get_().(Std_JSON_Values.JSON_Number).Num
    _ = _442___mcc_h2
    var _443_dec Std_JSON_Values.Decimal = _442___mcc_h2
    _ = _443_dec
    var _444_valueOrError1 Std_Wrappers.Result = Companion_Default___.Number(_443_dec)
    _ = _444_valueOrError1
    if ((_444_valueOrError1).IsFailure()) {
      return (_444_valueOrError1).PropagateFailure()
    } else {
      var _445_n Std_JSON_Grammar.Jnumber = (_444_valueOrError1).Extract().(Std_JSON_Grammar.Jnumber)
      _ = _445_n
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Value_.Create_Number_(_445_n))
    }
  } else if (_source16.Is_Object()) {
    var _446___mcc_h3 _dafny.Sequence = _source16.Get_().(Std_JSON_Values.JSON_Object).Obj
    _ = _446___mcc_h3
    var _447_obj _dafny.Sequence = _446___mcc_h3
    _ = _447_obj
    var _448_valueOrError2 Std_Wrappers.Result = Companion_Default___.Object(_447_obj)
    _ = _448_valueOrError2
    if ((_448_valueOrError2).IsFailure()) {
      return (_448_valueOrError2).PropagateFailure()
    } else {
      var _449_o Std_JSON_Grammar.Bracketed = (_448_valueOrError2).Extract().(Std_JSON_Grammar.Bracketed)
      _ = _449_o
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Value_.Create_Object_(_449_o))
    }
  } else {
    var _450___mcc_h4 _dafny.Sequence = _source16.Get_().(Std_JSON_Values.JSON_Array).Arr
    _ = _450___mcc_h4
    var _451_arr _dafny.Sequence = _450___mcc_h4
    _ = _451_arr
    var _452_valueOrError3 Std_Wrappers.Result = Companion_Default___.Array(_451_arr)
    _ = _452_valueOrError3
    if ((_452_valueOrError3).IsFailure()) {
      return (_452_valueOrError3).PropagateFailure()
    } else {
      var _453_a Std_JSON_Grammar.Bracketed = (_452_valueOrError3).Extract().(Std_JSON_Grammar.Bracketed)
      _ = _453_a
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Grammar.Companion_Value_.Create_Array_(_453_a))
    }
  }
}
func (_static *CompanionStruct_Default___) JSON(js Std_JSON_Values.JSON) Std_Wrappers.Result {
  var _454_valueOrError0 Std_Wrappers.Result = Companion_Default___.Value(js)
  _ = _454_valueOrError0
  if ((_454_valueOrError0).IsFailure()) {
    return (_454_valueOrError0).PropagateFailure()
  } else {
    var _455_val Std_JSON_Grammar.Value = (_454_valueOrError0).Extract().(Std_JSON_Grammar.Value)
    _ = _455_val
    return Std_Wrappers.Companion_Result_.Create_Success_(Companion_Default___.MkStructural(_455_val))
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
