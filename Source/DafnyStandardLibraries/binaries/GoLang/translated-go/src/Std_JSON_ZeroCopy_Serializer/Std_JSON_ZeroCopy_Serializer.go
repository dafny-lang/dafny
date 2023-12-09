// Package Std_JSON_ZeroCopy_Serializer
// Dafny module Std_JSON_ZeroCopy_Serializer compiled into Go

package Std_JSON_ZeroCopy_Serializer

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
  return "Std_JSON_ZeroCopy_Serializer.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) Serialize(js Std_JSON_Grammar.Structural) Std_Wrappers.Result {
  var rbs Std_Wrappers.Result = Std_Wrappers.Companion_Result_.Default(_dafny.NewArrayWithValue(nil, _dafny.IntOf(0)))
  _ = rbs
  var _550_writer Std_JSON_Utils_Views_Writers.Writer__
  _ = _550_writer
  _550_writer = Companion_Default___.Text(js)
  var _551_valueOrError0 Std_Wrappers.OutcomeResult = Std_Wrappers.Companion_OutcomeResult_.Default()
  _ = _551_valueOrError0
  _551_valueOrError0 = Std_Wrappers.Companion_Default___.Need((_550_writer).Unsaturated_q(), Std_JSON_Errors.Companion_SerializationError_.Create_OutOfMemory_())
  if ((_551_valueOrError0).IsFailure()) {
    rbs = (_551_valueOrError0).PropagateFailure()
    return rbs
  }
  var _552_bs _dafny.Array
  _ = _552_bs
  var _out6 _dafny.Array
  _ = _out6
  _out6 = (_550_writer).ToArray()
  _552_bs = _out6
  rbs = Std_Wrappers.Companion_Result_.Create_Success_(_552_bs)
  return rbs
  return rbs
}
func (_static *CompanionStruct_Default___) SerializeTo(js Std_JSON_Grammar.Structural, dest _dafny.Array) Std_Wrappers.Result {
  var len_ Std_Wrappers.Result = Std_Wrappers.Companion_Result_.Default(uint32(0))
  _ = len_
  var _553_writer Std_JSON_Utils_Views_Writers.Writer__
  _ = _553_writer
  _553_writer = Companion_Default___.Text(js)
  var _554_valueOrError0 Std_Wrappers.OutcomeResult = Std_Wrappers.Companion_OutcomeResult_.Default()
  _ = _554_valueOrError0
  _554_valueOrError0 = Std_Wrappers.Companion_Default___.Need((_553_writer).Unsaturated_q(), Std_JSON_Errors.Companion_SerializationError_.Create_OutOfMemory_())
  if ((_554_valueOrError0).IsFailure()) {
    len_ = (_554_valueOrError0).PropagateFailure()
    return len_
  }
  var _555_valueOrError1 Std_Wrappers.OutcomeResult = Std_Wrappers.Companion_OutcomeResult_.Default()
  _ = _555_valueOrError1
  _555_valueOrError1 = Std_Wrappers.Companion_Default___.Need((_dafny.IntOfUint32((_553_writer).Dtor_length())).Cmp(_dafny.ArrayLen((dest), 0)) <= 0, Std_JSON_Errors.Companion_SerializationError_.Create_OutOfMemory_())
  if ((_555_valueOrError1).IsFailure()) {
    len_ = (_555_valueOrError1).PropagateFailure()
    return len_
  }
  (_553_writer).CopyTo(dest)
  len_ = Std_Wrappers.Companion_Result_.Create_Success_((_553_writer).Dtor_length())
  return len_
  return len_
}
func (_static *CompanionStruct_Default___) Text(js Std_JSON_Grammar.Structural) Std_JSON_Utils_Views_Writers.Writer__ {
  return Companion_Default___.JSON(js, Std_JSON_Utils_Views_Writers.Companion_Writer___.Empty())
}
func (_static *CompanionStruct_Default___) JSON(js Std_JSON_Grammar.Structural, writer Std_JSON_Utils_Views_Writers.Writer__) Std_JSON_Utils_Views_Writers.Writer__ {
  return (((writer).Append((js).Dtor_before())).Then((func (_556_js Std_JSON_Grammar.Structural) func (Std_JSON_Utils_Views_Writers.Writer__) Std_JSON_Utils_Views_Writers.Writer__ {
    return func (_557_wr Std_JSON_Utils_Views_Writers.Writer__) Std_JSON_Utils_Views_Writers.Writer__ {
      return Companion_Default___.Value((_556_js).Dtor_t().(Std_JSON_Grammar.Value), _557_wr)
    }
  })(js))).Append((js).Dtor_after())
}
func (_static *CompanionStruct_Default___) Value(v Std_JSON_Grammar.Value, writer Std_JSON_Utils_Views_Writers.Writer__) Std_JSON_Utils_Views_Writers.Writer__ {
  var _source23 Std_JSON_Grammar.Value = v
  _ = _source23
  if (_source23.Is_Null()) {
    var _558___mcc_h0 Std_JSON_Utils_Views_Core.View__ = _source23.Get_().(Std_JSON_Grammar.Value_Null).N
    _ = _558___mcc_h0
    var _559_n Std_JSON_Utils_Views_Core.View__ = _558___mcc_h0
    _ = _559_n
    var _560_wr Std_JSON_Utils_Views_Writers.Writer__ = (writer).Append(_559_n)
    _ = _560_wr
    return _560_wr
  } else if (_source23.Is_Bool()) {
    var _561___mcc_h1 Std_JSON_Utils_Views_Core.View__ = _source23.Get_().(Std_JSON_Grammar.Value_Bool).B
    _ = _561___mcc_h1
    var _562_b Std_JSON_Utils_Views_Core.View__ = _561___mcc_h1
    _ = _562_b
    var _563_wr Std_JSON_Utils_Views_Writers.Writer__ = (writer).Append(_562_b)
    _ = _563_wr
    return _563_wr
  } else if (_source23.Is_String()) {
    var _564___mcc_h2 Std_JSON_Grammar.Jstring = _source23.Get_().(Std_JSON_Grammar.Value_String).Str
    _ = _564___mcc_h2
    var _565_str Std_JSON_Grammar.Jstring = _564___mcc_h2
    _ = _565_str
    var _566_wr Std_JSON_Utils_Views_Writers.Writer__ = Companion_Default___.String(_565_str, writer)
    _ = _566_wr
    return _566_wr
  } else if (_source23.Is_Number()) {
    var _567___mcc_h3 Std_JSON_Grammar.Jnumber = _source23.Get_().(Std_JSON_Grammar.Value_Number).Num
    _ = _567___mcc_h3
    var _568_num Std_JSON_Grammar.Jnumber = _567___mcc_h3
    _ = _568_num
    var _569_wr Std_JSON_Utils_Views_Writers.Writer__ = Companion_Default___.Number(_568_num, writer)
    _ = _569_wr
    return _569_wr
  } else if (_source23.Is_Object()) {
    var _570___mcc_h4 Std_JSON_Grammar.Bracketed = _source23.Get_().(Std_JSON_Grammar.Value_Object).Obj
    _ = _570___mcc_h4
    var _571_obj Std_JSON_Grammar.Bracketed = _570___mcc_h4
    _ = _571_obj
    var _572_wr Std_JSON_Utils_Views_Writers.Writer__ = Companion_Default___.Object(_571_obj, writer)
    _ = _572_wr
    return _572_wr
  } else {
    var _573___mcc_h5 Std_JSON_Grammar.Bracketed = _source23.Get_().(Std_JSON_Grammar.Value_Array).Arr
    _ = _573___mcc_h5
    var _574_arr Std_JSON_Grammar.Bracketed = _573___mcc_h5
    _ = _574_arr
    var _575_wr Std_JSON_Utils_Views_Writers.Writer__ = Companion_Default___.Array(_574_arr, writer)
    _ = _575_wr
    return _575_wr
  }
}
func (_static *CompanionStruct_Default___) String(str Std_JSON_Grammar.Jstring, writer Std_JSON_Utils_Views_Writers.Writer__) Std_JSON_Utils_Views_Writers.Writer__ {
  return (((writer).Append((str).Dtor_lq())).Append((str).Dtor_contents())).Append((str).Dtor_rq())
}
func (_static *CompanionStruct_Default___) Number(num Std_JSON_Grammar.Jnumber, writer Std_JSON_Utils_Views_Writers.Writer__) Std_JSON_Utils_Views_Writers.Writer__ {
  var _576_wr1 Std_JSON_Utils_Views_Writers.Writer__ = ((writer).Append((num).Dtor_minus())).Append((num).Dtor_num())
  _ = _576_wr1
  var _577_wr2 Std_JSON_Utils_Views_Writers.Writer__ = (func () Std_JSON_Utils_Views_Writers.Writer__ { if ((num).Dtor_frac()).Is_NonEmpty() { return ((_576_wr1).Append((((num).Dtor_frac()).Dtor_t().(Std_JSON_Grammar.Jfrac)).Dtor_period())).Append((((num).Dtor_frac()).Dtor_t().(Std_JSON_Grammar.Jfrac)).Dtor_num()) }; return _576_wr1 })() 
  _ = _577_wr2
  var _578_wr3 Std_JSON_Utils_Views_Writers.Writer__ = (func () Std_JSON_Utils_Views_Writers.Writer__ { if ((num).Dtor_exp()).Is_NonEmpty() { return (((_577_wr2).Append((((num).Dtor_exp()).Dtor_t().(Std_JSON_Grammar.Jexp)).Dtor_e())).Append((((num).Dtor_exp()).Dtor_t().(Std_JSON_Grammar.Jexp)).Dtor_sign())).Append((((num).Dtor_exp()).Dtor_t().(Std_JSON_Grammar.Jexp)).Dtor_num()) }; return _577_wr2 })() 
  _ = _578_wr3
  var _579_wr Std_JSON_Utils_Views_Writers.Writer__ = _578_wr3
  _ = _579_wr
  return _579_wr
}
func (_static *CompanionStruct_Default___) StructuralView(st Std_JSON_Grammar.Structural, writer Std_JSON_Utils_Views_Writers.Writer__) Std_JSON_Utils_Views_Writers.Writer__ {
  return (((writer).Append((st).Dtor_before())).Append((st).Dtor_t().(Std_JSON_Utils_Views_Core.View__))).Append((st).Dtor_after())
}
func (_static *CompanionStruct_Default___) Object(obj Std_JSON_Grammar.Bracketed, writer Std_JSON_Utils_Views_Writers.Writer__) Std_JSON_Utils_Views_Writers.Writer__ {
  var _580_wr Std_JSON_Utils_Views_Writers.Writer__ = Companion_Default___.StructuralView((obj).Dtor_l(), writer)
  _ = _580_wr
  var _581_wr Std_JSON_Utils_Views_Writers.Writer__ = Companion_Default___.Members(obj, _580_wr)
  _ = _581_wr
  var _582_wr Std_JSON_Utils_Views_Writers.Writer__ = Companion_Default___.StructuralView((obj).Dtor_r(), _581_wr)
  _ = _582_wr
  return _582_wr
}
func (_static *CompanionStruct_Default___) Array(arr Std_JSON_Grammar.Bracketed, writer Std_JSON_Utils_Views_Writers.Writer__) Std_JSON_Utils_Views_Writers.Writer__ {
  var _583_wr Std_JSON_Utils_Views_Writers.Writer__ = Companion_Default___.StructuralView((arr).Dtor_l(), writer)
  _ = _583_wr
  var _584_wr Std_JSON_Utils_Views_Writers.Writer__ = Companion_Default___.Items(arr, _583_wr)
  _ = _584_wr
  var _585_wr Std_JSON_Utils_Views_Writers.Writer__ = Companion_Default___.StructuralView((arr).Dtor_r(), _584_wr)
  _ = _585_wr
  return _585_wr
}
func (_static *CompanionStruct_Default___) Members(obj Std_JSON_Grammar.Bracketed, writer Std_JSON_Utils_Views_Writers.Writer__) Std_JSON_Utils_Views_Writers.Writer__ {
  var wr Std_JSON_Utils_Views_Writers.Writer__ = Std_JSON_Utils_Views_Writers.Companion_Writer_.Witness()
  _ = wr
  var _out7 Std_JSON_Utils_Views_Writers.Writer__
  _ = _out7
  _out7 = Companion_Default___.MembersImpl(obj, writer)
  wr = _out7
  return wr
}
func (_static *CompanionStruct_Default___) Items(arr Std_JSON_Grammar.Bracketed, writer Std_JSON_Utils_Views_Writers.Writer__) Std_JSON_Utils_Views_Writers.Writer__ {
  var wr Std_JSON_Utils_Views_Writers.Writer__ = Std_JSON_Utils_Views_Writers.Companion_Writer_.Witness()
  _ = wr
  var _out8 Std_JSON_Utils_Views_Writers.Writer__
  _ = _out8
  _out8 = Companion_Default___.ItemsImpl(arr, writer)
  wr = _out8
  return wr
}
func (_static *CompanionStruct_Default___) MembersImpl(obj Std_JSON_Grammar.Bracketed, writer Std_JSON_Utils_Views_Writers.Writer__) Std_JSON_Utils_Views_Writers.Writer__ {
  var wr Std_JSON_Utils_Views_Writers.Writer__ = Std_JSON_Utils_Views_Writers.Companion_Writer_.Witness()
  _ = wr
  wr = writer
  var _586_members _dafny.Sequence
  _ = _586_members
  _586_members = (obj).Dtor_data()
  var _hi1 _dafny.Int = _dafny.IntOfUint32((_586_members).Cardinality())
  _ = _hi1
  for _587_i := _dafny.Zero; _587_i.Cmp(_hi1) < 0; _587_i = _587_i.Plus(_dafny.One) {
    wr = Companion_Default___.Member((_586_members).Select((_587_i).Uint32()).(Std_JSON_Grammar.Suffixed), wr)
  }
  return wr
}
func (_static *CompanionStruct_Default___) ItemsImpl(arr Std_JSON_Grammar.Bracketed, writer Std_JSON_Utils_Views_Writers.Writer__) Std_JSON_Utils_Views_Writers.Writer__ {
  var wr Std_JSON_Utils_Views_Writers.Writer__ = Std_JSON_Utils_Views_Writers.Companion_Writer_.Witness()
  _ = wr
  wr = writer
  var _588_items _dafny.Sequence
  _ = _588_items
  _588_items = (arr).Dtor_data()
  var _hi2 _dafny.Int = _dafny.IntOfUint32((_588_items).Cardinality())
  _ = _hi2
  for _589_i := _dafny.Zero; _589_i.Cmp(_hi2) < 0; _589_i = _589_i.Plus(_dafny.One) {
    wr = Companion_Default___.Item((_588_items).Select((_589_i).Uint32()).(Std_JSON_Grammar.Suffixed), wr)
  }
  return wr
}
func (_static *CompanionStruct_Default___) Member(m Std_JSON_Grammar.Suffixed, writer Std_JSON_Utils_Views_Writers.Writer__) Std_JSON_Utils_Views_Writers.Writer__ {
  var _590_wr Std_JSON_Utils_Views_Writers.Writer__ = Companion_Default___.String(((m).Dtor_t().(Std_JSON_Grammar.JKeyValue)).Dtor_k(), writer)
  _ = _590_wr
  var _591_wr Std_JSON_Utils_Views_Writers.Writer__ = Companion_Default___.StructuralView(((m).Dtor_t().(Std_JSON_Grammar.JKeyValue)).Dtor_colon(), _590_wr)
  _ = _591_wr
  var _592_wr Std_JSON_Utils_Views_Writers.Writer__ = Companion_Default___.Value(((m).Dtor_t().(Std_JSON_Grammar.JKeyValue)).Dtor_v(), _591_wr)
  _ = _592_wr
  var _593_wr Std_JSON_Utils_Views_Writers.Writer__ = (func () Std_JSON_Utils_Views_Writers.Writer__ { if ((m).Dtor_suffix()).Is_Empty() { return _592_wr }; return Companion_Default___.StructuralView(((m).Dtor_suffix()).Dtor_t().(Std_JSON_Grammar.Structural), _592_wr) })() 
  _ = _593_wr
  return _593_wr
}
func (_static *CompanionStruct_Default___) Item(m Std_JSON_Grammar.Suffixed, writer Std_JSON_Utils_Views_Writers.Writer__) Std_JSON_Utils_Views_Writers.Writer__ {
  var _594_wr Std_JSON_Utils_Views_Writers.Writer__ = Companion_Default___.Value((m).Dtor_t().(Std_JSON_Grammar.Value), writer)
  _ = _594_wr
  var _595_wr Std_JSON_Utils_Views_Writers.Writer__ = (func () Std_JSON_Utils_Views_Writers.Writer__ { if ((m).Dtor_suffix()).Is_Empty() { return _594_wr }; return Companion_Default___.StructuralView(((m).Dtor_suffix()).Dtor_t().(Std_JSON_Grammar.Structural), _594_wr) })() 
  _ = _595_wr
  return _595_wr
}
// End of class Default__
