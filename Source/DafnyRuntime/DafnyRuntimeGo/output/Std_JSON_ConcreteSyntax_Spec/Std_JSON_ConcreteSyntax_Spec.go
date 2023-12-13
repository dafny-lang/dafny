// Package Std_JSON_ConcreteSyntax_Spec
// Dafny module Std_JSON_ConcreteSyntax_Spec compiled into Go

package Std_JSON_ConcreteSyntax_Spec

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
  return "Std_JSON_ConcreteSyntax_Spec.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) View(v Std_JSON_Utils_Views_Core.View__) _dafny.Sequence {
  return (v).Bytes()
}
func (_static *CompanionStruct_Default___) Structural(self Std_JSON_Grammar.Structural, fT func (interface{}) _dafny.Sequence) _dafny.Sequence {
  return _dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(Companion_Default___.View((self).Dtor_before()), (fT)((self).Dtor_t())), Companion_Default___.View((self).Dtor_after()))
}
func (_static *CompanionStruct_Default___) StructuralView(self Std_JSON_Grammar.Structural) _dafny.Sequence {
  return Companion_Default___.Structural(self, func (coer36 func (Std_JSON_Utils_Views_Core.View__) _dafny.Sequence) func (interface{}) _dafny.Sequence {
    return func (arg38 interface{}) _dafny.Sequence {
      return coer36(arg38.(Std_JSON_Utils_Views_Core.View__))
    }
  }(Companion_Default___.View))
}
func (_static *CompanionStruct_Default___) Maybe(self Std_JSON_Grammar.Maybe, fT func (interface{}) _dafny.Sequence) _dafny.Sequence {
  if ((self).Is_Empty()) {
    return _dafny.SeqOf()
  } else {
    return (fT)((self).Dtor_t())
  }
}
func (_static *CompanionStruct_Default___) ConcatBytes(ts _dafny.Sequence, fT func (interface{}) _dafny.Sequence) _dafny.Sequence {
  var _541___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _541___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((ts).Cardinality())).Sign() == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_541___accumulator, _dafny.SeqOf())
  } else {
    _541___accumulator = _dafny.Companion_Sequence_.Concatenate(_541___accumulator, (fT)((ts).Select(0).(interface{})))
    var _in95 _dafny.Sequence = (ts).Drop(1)
    _ = _in95
    var _in96 func (interface{}) _dafny.Sequence = fT
    _ = _in96
    ts = _in95
    fT = _in96
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) Bracketed(self Std_JSON_Grammar.Bracketed, fDatum func (Std_JSON_Grammar.Suffixed) _dafny.Sequence) _dafny.Sequence {
  return _dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(Companion_Default___.StructuralView((self).Dtor_l()), Companion_Default___.ConcatBytes((self).Dtor_data(), func (coer37 func (Std_JSON_Grammar.Suffixed) _dafny.Sequence) func (interface{}) _dafny.Sequence {
    return func (arg39 interface{}) _dafny.Sequence {
      return coer37(arg39.(Std_JSON_Grammar.Suffixed))
    }
  }(fDatum))), Companion_Default___.StructuralView((self).Dtor_r()))
}
func (_static *CompanionStruct_Default___) KeyValue(self Std_JSON_Grammar.JKeyValue) _dafny.Sequence {
  return _dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(Companion_Default___.String((self).Dtor_k()), Companion_Default___.StructuralView((self).Dtor_colon())), Companion_Default___.Value((self).Dtor_v()))
}
func (_static *CompanionStruct_Default___) Frac(self Std_JSON_Grammar.Jfrac) _dafny.Sequence {
  return _dafny.Companion_Sequence_.Concatenate(Companion_Default___.View((self).Dtor_period()), Companion_Default___.View((self).Dtor_num()))
}
func (_static *CompanionStruct_Default___) Exp(self Std_JSON_Grammar.Jexp) _dafny.Sequence {
  return _dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(Companion_Default___.View((self).Dtor_e()), Companion_Default___.View((self).Dtor_sign())), Companion_Default___.View((self).Dtor_num()))
}
func (_static *CompanionStruct_Default___) Number(self Std_JSON_Grammar.Jnumber) _dafny.Sequence {
  return _dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(Companion_Default___.View((self).Dtor_minus()), Companion_Default___.View((self).Dtor_num())), Companion_Default___.Maybe((self).Dtor_frac(), func (coer38 func (Std_JSON_Grammar.Jfrac) _dafny.Sequence) func (interface{}) _dafny.Sequence {
    return func (arg40 interface{}) _dafny.Sequence {
      return coer38(arg40.(Std_JSON_Grammar.Jfrac))
    }
  }(Companion_Default___.Frac))), Companion_Default___.Maybe((self).Dtor_exp(), func (coer39 func (Std_JSON_Grammar.Jexp) _dafny.Sequence) func (interface{}) _dafny.Sequence {
    return func (arg41 interface{}) _dafny.Sequence {
      return coer39(arg41.(Std_JSON_Grammar.Jexp))
    }
  }(Companion_Default___.Exp)))
}
func (_static *CompanionStruct_Default___) String(self Std_JSON_Grammar.Jstring) _dafny.Sequence {
  return _dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate(Companion_Default___.View((self).Dtor_lq()), Companion_Default___.View((self).Dtor_contents())), Companion_Default___.View((self).Dtor_rq()))
}
func (_static *CompanionStruct_Default___) CommaSuffix(c Std_JSON_Grammar.Maybe) _dafny.Sequence {
  return Companion_Default___.Maybe(c, func (coer40 func (Std_JSON_Grammar.Structural) _dafny.Sequence) func (interface{}) _dafny.Sequence {
    return func (arg42 interface{}) _dafny.Sequence {
      return coer40(arg42.(Std_JSON_Grammar.Structural))
    }
  }(Companion_Default___.StructuralView))
}
func (_static *CompanionStruct_Default___) Member(self Std_JSON_Grammar.Suffixed) _dafny.Sequence {
  return _dafny.Companion_Sequence_.Concatenate(Companion_Default___.KeyValue((self).Dtor_t().(Std_JSON_Grammar.JKeyValue)), Companion_Default___.CommaSuffix((self).Dtor_suffix()))
}
func (_static *CompanionStruct_Default___) Item(self Std_JSON_Grammar.Suffixed) _dafny.Sequence {
  return _dafny.Companion_Sequence_.Concatenate(Companion_Default___.Value((self).Dtor_t().(Std_JSON_Grammar.Value)), Companion_Default___.CommaSuffix((self).Dtor_suffix()))
}
func (_static *CompanionStruct_Default___) Object(obj Std_JSON_Grammar.Bracketed) _dafny.Sequence {
  return Companion_Default___.Bracketed(obj, func (coer41 func (Std_JSON_Grammar.Suffixed) _dafny.Sequence) func (Std_JSON_Grammar.Suffixed) _dafny.Sequence {
    return func (arg43 Std_JSON_Grammar.Suffixed) _dafny.Sequence {
      return coer41(arg43)
    }
  }((func (_542_obj Std_JSON_Grammar.Bracketed) func (Std_JSON_Grammar.Suffixed) _dafny.Sequence {
    return func (_543_d Std_JSON_Grammar.Suffixed) _dafny.Sequence {
      return Companion_Default___.Member(_543_d)
    }
  })(obj)))
}
func (_static *CompanionStruct_Default___) Array(arr Std_JSON_Grammar.Bracketed) _dafny.Sequence {
  return Companion_Default___.Bracketed(arr, func (coer42 func (Std_JSON_Grammar.Suffixed) _dafny.Sequence) func (Std_JSON_Grammar.Suffixed) _dafny.Sequence {
    return func (arg44 Std_JSON_Grammar.Suffixed) _dafny.Sequence {
      return coer42(arg44)
    }
  }((func (_544_arr Std_JSON_Grammar.Bracketed) func (Std_JSON_Grammar.Suffixed) _dafny.Sequence {
    return func (_545_d Std_JSON_Grammar.Suffixed) _dafny.Sequence {
      return Companion_Default___.Item(_545_d)
    }
  })(arr)))
}
func (_static *CompanionStruct_Default___) Value(self Std_JSON_Grammar.Value) _dafny.Sequence {
  var _source22 Std_JSON_Grammar.Value = self
  _ = _source22
  if (_source22.Is_Null()) {
    var _546___mcc_h0 Std_JSON_Utils_Views_Core.View__ = _source22.Get_().(Std_JSON_Grammar.Value_Null).N
    _ = _546___mcc_h0
    var _547_n Std_JSON_Utils_Views_Core.View__ = _546___mcc_h0
    _ = _547_n
    return Companion_Default___.View(_547_n)
  } else if (_source22.Is_Bool()) {
    var _548___mcc_h1 Std_JSON_Utils_Views_Core.View__ = _source22.Get_().(Std_JSON_Grammar.Value_Bool).B
    _ = _548___mcc_h1
    var _549_b Std_JSON_Utils_Views_Core.View__ = _548___mcc_h1
    _ = _549_b
    return Companion_Default___.View(_549_b)
  } else if (_source22.Is_String()) {
    var _550___mcc_h2 Std_JSON_Grammar.Jstring = _source22.Get_().(Std_JSON_Grammar.Value_String).Str
    _ = _550___mcc_h2
    var _551_str Std_JSON_Grammar.Jstring = _550___mcc_h2
    _ = _551_str
    return Companion_Default___.String(_551_str)
  } else if (_source22.Is_Number()) {
    var _552___mcc_h3 Std_JSON_Grammar.Jnumber = _source22.Get_().(Std_JSON_Grammar.Value_Number).Num
    _ = _552___mcc_h3
    var _553_num Std_JSON_Grammar.Jnumber = _552___mcc_h3
    _ = _553_num
    return Companion_Default___.Number(_553_num)
  } else if (_source22.Is_Object()) {
    var _554___mcc_h4 Std_JSON_Grammar.Bracketed = _source22.Get_().(Std_JSON_Grammar.Value_Object).Obj
    _ = _554___mcc_h4
    var _555_obj Std_JSON_Grammar.Bracketed = _554___mcc_h4
    _ = _555_obj
    return Companion_Default___.Object(_555_obj)
  } else {
    var _556___mcc_h5 Std_JSON_Grammar.Bracketed = _source22.Get_().(Std_JSON_Grammar.Value_Array).Arr
    _ = _556___mcc_h5
    var _557_arr Std_JSON_Grammar.Bracketed = _556___mcc_h5
    _ = _557_arr
    return Companion_Default___.Array(_557_arr)
  }
}
func (_static *CompanionStruct_Default___) JSON(js Std_JSON_Grammar.Structural) _dafny.Sequence {
  return Companion_Default___.Structural(js, func (coer43 func (Std_JSON_Grammar.Value) _dafny.Sequence) func (interface{}) _dafny.Sequence {
    return func (arg45 interface{}) _dafny.Sequence {
      return coer43(arg45.(Std_JSON_Grammar.Value))
    }
  }(Companion_Default___.Value))
}
// End of class Default__
