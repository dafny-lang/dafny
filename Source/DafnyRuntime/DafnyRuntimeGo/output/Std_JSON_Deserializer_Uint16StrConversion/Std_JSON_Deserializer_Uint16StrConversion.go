// Package Std_JSON_Deserializer_Uint16StrConversion
// Dafny module Std_JSON_Deserializer_Uint16StrConversion compiled into Go

package Std_JSON_Deserializer_Uint16StrConversion

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
  return "Std_JSON_Deserializer_Uint16StrConversion.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) BASE() _dafny.Int {
  return Companion_Default___.Base()
}
func (_static *CompanionStruct_Default___) IsDigitChar(c uint16) bool {
  return (Companion_Default___.CharToDigit()).Contains(c)
}
func (_static *CompanionStruct_Default___) OfDigits(digits _dafny.Sequence) _dafny.Sequence {
  var _464___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _464___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if (_dafny.Companion_Sequence_.Equal(digits, _dafny.SeqOf())) {
    return _dafny.Companion_Sequence_.Concatenate(_dafny.SeqOf(), _464___accumulator)
  } else {
    _464___accumulator = _dafny.Companion_Sequence_.Concatenate(_dafny.SeqOf((Companion_Default___.Chars()).Select(((digits).Select(0).(_dafny.Int)).Uint32()).(uint16)), _464___accumulator)
    var _in81 _dafny.Sequence = (digits).Drop(1)
    _ = _in81
    digits = _in81
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) OfNat(n _dafny.Int) _dafny.Sequence {
  if ((n).Sign() == 0) {
    return _dafny.SeqOf((Companion_Default___.Chars()).Select(0).(uint16))
  } else {
    return Companion_Default___.OfDigits(Companion_Default___.FromNat(n))
  }
}
func (_static *CompanionStruct_Default___) IsNumberStr(str _dafny.Sequence, minus uint16) bool {
  return !(!_dafny.Companion_Sequence_.Equal(str, _dafny.SeqOf())) || (((((str).Select(0).(uint16)) == (minus)) || ((Companion_Default___.CharToDigit()).Contains((str).Select(0).(uint16)))) && (_dafny.Quantifier(((str).Drop(1)).UniqueElements(), true, func (_forall_var_4 uint16) bool {
    var _465_c uint16
    _465_c = interface{}(_forall_var_4).(uint16)
    return !(_dafny.Companion_Sequence_.Contains((str).Drop(1), _465_c)) || (Companion_Default___.IsDigitChar(_465_c))
  })))
}
func (_static *CompanionStruct_Default___) OfInt(n _dafny.Int, minus uint16) _dafny.Sequence {
  if ((n).Sign() != -1) {
    return Companion_Default___.OfNat(n)
  } else {
    return _dafny.Companion_Sequence_.Concatenate(_dafny.SeqOf(minus), Companion_Default___.OfNat((_dafny.Zero).Minus(n)))
  }
}
func (_static *CompanionStruct_Default___) ToNat(str _dafny.Sequence) _dafny.Int {
  if (_dafny.Companion_Sequence_.Equal(str, _dafny.SeqOf())) {
    return _dafny.Zero
  } else {
    var _466_c uint16 = (str).Select(((_dafny.IntOfUint32((str).Cardinality())).Minus(_dafny.One)).Uint32()).(uint16)
    _ = _466_c
    return ((Companion_Default___.ToNat((str).Take(((_dafny.IntOfUint32((str).Cardinality())).Minus(_dafny.One)).Uint32()))).Times(Companion_Default___.Base())).Plus((Companion_Default___.CharToDigit()).Get(_466_c).(_dafny.Int))
  }
}
func (_static *CompanionStruct_Default___) ToInt(str _dafny.Sequence, minus uint16) _dafny.Int {
  if (_dafny.Companion_Sequence_.IsPrefixOf(_dafny.SeqOf(minus), str)) {
    return (_dafny.Zero).Minus((Companion_Default___.ToNat((str).Drop(1))))
  } else {
    return Companion_Default___.ToNat(str)
  }
}
func (_static *CompanionStruct_Default___) ToNatRight(xs _dafny.Sequence) _dafny.Int {
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return _dafny.Zero
  } else {
    return ((Companion_Default___.ToNatRight(Std_Collections_Seq.Companion_Default___.DropFirst(xs))).Times(Companion_Default___.BASE())).Plus(Std_Collections_Seq.Companion_Default___.First(xs).(_dafny.Int))
  }
}
func (_static *CompanionStruct_Default___) ToNatLeft(xs _dafny.Sequence) _dafny.Int {
  var _467___accumulator _dafny.Int = _dafny.Zero
  _ = _467___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return (_dafny.Zero).Plus(_467___accumulator)
  } else {
    _467___accumulator = ((Std_Collections_Seq.Companion_Default___.Last(xs).(_dafny.Int)).Times(Std_Arithmetic_Power.Companion_Default___.Pow(Companion_Default___.BASE(), (_dafny.IntOfUint32((xs).Cardinality())).Minus(_dafny.One)))).Plus(_467___accumulator)
    var _in82 _dafny.Sequence = Std_Collections_Seq.Companion_Default___.DropLast(xs)
    _ = _in82
    xs = _in82
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) FromNat(n _dafny.Int) _dafny.Sequence {
  var _468___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _468___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((n).Sign() == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_468___accumulator, _dafny.SeqOf())
  } else {
    _468___accumulator = _dafny.Companion_Sequence_.Concatenate(_468___accumulator, _dafny.SeqOf((n).Modulo(Companion_Default___.BASE())))
    var _in83 _dafny.Int = (n).DivBy(Companion_Default___.BASE())
    _ = _in83
    n = _in83
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) SeqExtend(xs _dafny.Sequence, n _dafny.Int) _dafny.Sequence {
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((xs).Cardinality())).Cmp(n) >= 0) {
    return xs
  } else {
    var _in84 _dafny.Sequence = _dafny.Companion_Sequence_.Concatenate(xs, _dafny.SeqOf(_dafny.Zero))
    _ = _in84
    var _in85 _dafny.Int = n
    _ = _in85
    xs = _in84
    n = _in85
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) SeqExtendMultiple(xs _dafny.Sequence, n _dafny.Int) _dafny.Sequence {
  var _469_newLen _dafny.Int = ((_dafny.IntOfUint32((xs).Cardinality())).Plus(n)).Minus((_dafny.IntOfUint32((xs).Cardinality())).Modulo(n))
  _ = _469_newLen
  return Companion_Default___.SeqExtend(xs, _469_newLen)
}
func (_static *CompanionStruct_Default___) FromNatWithLen(n _dafny.Int, len_ _dafny.Int) _dafny.Sequence {
  return Companion_Default___.SeqExtend(Companion_Default___.FromNat(n), len_)
}
func (_static *CompanionStruct_Default___) SeqZero(len_ _dafny.Int) _dafny.Sequence {
  var _470_xs _dafny.Sequence = Companion_Default___.FromNatWithLen(_dafny.Zero, len_)
  _ = _470_xs
  return _470_xs
}
func (_static *CompanionStruct_Default___) SeqAdd(xs _dafny.Sequence, ys _dafny.Sequence) _dafny.Tuple {
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return _dafny.TupleOf(_dafny.SeqOf(), _dafny.Zero)
  } else {
    var _let_tmp_rhs13 _dafny.Tuple = Companion_Default___.SeqAdd(Std_Collections_Seq.Companion_Default___.DropLast(xs), Std_Collections_Seq.Companion_Default___.DropLast(ys))
    _ = _let_tmp_rhs13
    var _471_zs_k _dafny.Sequence = (*(_let_tmp_rhs13).IndexInt(0)).(_dafny.Sequence)
    _ = _471_zs_k
    var _472_cin _dafny.Int = (*(_let_tmp_rhs13).IndexInt(1)).(_dafny.Int)
    _ = _472_cin
    var _473_sum _dafny.Int = ((Std_Collections_Seq.Companion_Default___.Last(xs).(_dafny.Int)).Plus(Std_Collections_Seq.Companion_Default___.Last(ys).(_dafny.Int))).Plus(_472_cin)
    _ = _473_sum
    var _let_tmp_rhs14 _dafny.Tuple = (func () _dafny.Tuple { if (_473_sum).Cmp(Companion_Default___.BASE()) < 0 { return _dafny.TupleOf(_473_sum, _dafny.Zero) }; return _dafny.TupleOf((_473_sum).Minus(Companion_Default___.BASE()), _dafny.One) })() 
    _ = _let_tmp_rhs14
    var _474_sum__out _dafny.Int = (*(_let_tmp_rhs14).IndexInt(0)).(_dafny.Int)
    _ = _474_sum__out
    var _475_cout _dafny.Int = (*(_let_tmp_rhs14).IndexInt(1)).(_dafny.Int)
    _ = _475_cout
    return _dafny.TupleOf(_dafny.Companion_Sequence_.Concatenate(_471_zs_k, _dafny.SeqOf(_474_sum__out)), _475_cout)
  }
}
func (_static *CompanionStruct_Default___) SeqSub(xs _dafny.Sequence, ys _dafny.Sequence) _dafny.Tuple {
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return _dafny.TupleOf(_dafny.SeqOf(), _dafny.Zero)
  } else {
    var _let_tmp_rhs15 _dafny.Tuple = Companion_Default___.SeqSub(Std_Collections_Seq.Companion_Default___.DropLast(xs), Std_Collections_Seq.Companion_Default___.DropLast(ys))
    _ = _let_tmp_rhs15
    var _476_zs _dafny.Sequence = (*(_let_tmp_rhs15).IndexInt(0)).(_dafny.Sequence)
    _ = _476_zs
    var _477_cin _dafny.Int = (*(_let_tmp_rhs15).IndexInt(1)).(_dafny.Int)
    _ = _477_cin
    var _let_tmp_rhs16 _dafny.Tuple = (func () _dafny.Tuple { if (Std_Collections_Seq.Companion_Default___.Last(xs).(_dafny.Int)).Cmp((Std_Collections_Seq.Companion_Default___.Last(ys).(_dafny.Int)).Plus(_477_cin)) >= 0 { return _dafny.TupleOf(((Std_Collections_Seq.Companion_Default___.Last(xs).(_dafny.Int)).Minus(Std_Collections_Seq.Companion_Default___.Last(ys).(_dafny.Int))).Minus(_477_cin), _dafny.Zero) }; return _dafny.TupleOf((((Companion_Default___.BASE()).Plus(Std_Collections_Seq.Companion_Default___.Last(xs).(_dafny.Int))).Minus(Std_Collections_Seq.Companion_Default___.Last(ys).(_dafny.Int))).Minus(_477_cin), _dafny.One) })() 
    _ = _let_tmp_rhs16
    var _478_diff__out _dafny.Int = (*(_let_tmp_rhs16).IndexInt(0)).(_dafny.Int)
    _ = _478_diff__out
    var _479_cout _dafny.Int = (*(_let_tmp_rhs16).IndexInt(1)).(_dafny.Int)
    _ = _479_cout
    return _dafny.TupleOf(_dafny.Companion_Sequence_.Concatenate(_476_zs, _dafny.SeqOf(_478_diff__out)), _479_cout)
  }
}
func (_static *CompanionStruct_Default___) Chars() _dafny.Sequence {
  return _dafny.SeqOf(uint16(_dafny.CodePoint('0')), uint16(_dafny.CodePoint('1')), uint16(_dafny.CodePoint('2')), uint16(_dafny.CodePoint('3')), uint16(_dafny.CodePoint('4')), uint16(_dafny.CodePoint('5')), uint16(_dafny.CodePoint('6')), uint16(_dafny.CodePoint('7')), uint16(_dafny.CodePoint('8')), uint16(_dafny.CodePoint('9')), uint16(_dafny.CodePoint('a')), uint16(_dafny.CodePoint('b')), uint16(_dafny.CodePoint('c')), uint16(_dafny.CodePoint('d')), uint16(_dafny.CodePoint('e')), uint16(_dafny.CodePoint('f')), uint16(_dafny.CodePoint('A')), uint16(_dafny.CodePoint('B')), uint16(_dafny.CodePoint('C')), uint16(_dafny.CodePoint('D')), uint16(_dafny.CodePoint('E')), uint16(_dafny.CodePoint('F')))
}
func (_static *CompanionStruct_Default___) Base() _dafny.Int {
  return _dafny.IntOfUint32((Companion_Default___.Chars()).Cardinality())
}
func (_static *CompanionStruct_Default___) CharToDigit() _dafny.Map {
  return _dafny.NewMapBuilder().ToMap().UpdateUnsafe(uint16(_dafny.CodePoint('0')), _dafny.Zero).UpdateUnsafe(uint16(_dafny.CodePoint('1')), _dafny.One).UpdateUnsafe(uint16(_dafny.CodePoint('2')), _dafny.IntOfInt64(2)).UpdateUnsafe(uint16(_dafny.CodePoint('3')), _dafny.IntOfInt64(3)).UpdateUnsafe(uint16(_dafny.CodePoint('4')), _dafny.IntOfInt64(4)).UpdateUnsafe(uint16(_dafny.CodePoint('5')), _dafny.IntOfInt64(5)).UpdateUnsafe(uint16(_dafny.CodePoint('6')), _dafny.IntOfInt64(6)).UpdateUnsafe(uint16(_dafny.CodePoint('7')), _dafny.IntOfInt64(7)).UpdateUnsafe(uint16(_dafny.CodePoint('8')), _dafny.IntOfInt64(8)).UpdateUnsafe(uint16(_dafny.CodePoint('9')), _dafny.IntOfInt64(9)).UpdateUnsafe(uint16(_dafny.CodePoint('a')), _dafny.IntOfInt64(10)).UpdateUnsafe(uint16(_dafny.CodePoint('b')), _dafny.IntOfInt64(11)).UpdateUnsafe(uint16(_dafny.CodePoint('c')), _dafny.IntOfInt64(12)).UpdateUnsafe(uint16(_dafny.CodePoint('d')), _dafny.IntOfInt64(13)).UpdateUnsafe(uint16(_dafny.CodePoint('e')), _dafny.IntOfInt64(14)).UpdateUnsafe(uint16(_dafny.CodePoint('f')), _dafny.IntOfInt64(15)).UpdateUnsafe(uint16(_dafny.CodePoint('A')), _dafny.IntOfInt64(10)).UpdateUnsafe(uint16(_dafny.CodePoint('B')), _dafny.IntOfInt64(11)).UpdateUnsafe(uint16(_dafny.CodePoint('C')), _dafny.IntOfInt64(12)).UpdateUnsafe(uint16(_dafny.CodePoint('D')), _dafny.IntOfInt64(13)).UpdateUnsafe(uint16(_dafny.CodePoint('E')), _dafny.IntOfInt64(14)).UpdateUnsafe(uint16(_dafny.CodePoint('F')), _dafny.IntOfInt64(15))
}
// End of class Default__

// Definition of class CharSeq
type CharSeq struct {
}

func New_CharSeq_() *CharSeq {
  _this := CharSeq{}

  return &_this
}

type CompanionStruct_CharSeq_ struct {
}
var Companion_CharSeq_ = CompanionStruct_CharSeq_ {
}

func (*CharSeq) String() string {
  return "Std_JSON_Deserializer_Uint16StrConversion.CharSeq"
}
// End of class CharSeq

func Type_CharSeq_() _dafny.TypeDescriptor {
  return type_CharSeq_{}
}

type type_CharSeq_ struct {
}

func (_this type_CharSeq_) Default() interface{} {
  return _dafny.EmptySeq
}

func (_this type_CharSeq_) String() string {
  return "Std_JSON_Deserializer_Uint16StrConversion.CharSeq"
}

// Definition of class Digit
type Digit struct {
}

func New_Digit_() *Digit {
  _this := Digit{}

  return &_this
}

type CompanionStruct_Digit_ struct {
}
var Companion_Digit_ = CompanionStruct_Digit_ {
}

func (*Digit) String() string {
  return "Std_JSON_Deserializer_Uint16StrConversion.Digit"
}
// End of class Digit

func Type_Digit_() _dafny.TypeDescriptor {
  return type_Digit_{}
}

type type_Digit_ struct {
}

func (_this type_Digit_) Default() interface{} {
  return _dafny.Zero
}

func (_this type_Digit_) String() string {
  return "Std_JSON_Deserializer_Uint16StrConversion.Digit"
}
