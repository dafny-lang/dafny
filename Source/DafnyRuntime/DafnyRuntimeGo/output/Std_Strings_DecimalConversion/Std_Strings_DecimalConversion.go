// Package Std_Strings_DecimalConversion
// Dafny module Std_Strings_DecimalConversion compiled into Go

package Std_Strings_DecimalConversion

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
  return "Std_Strings_DecimalConversion.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) BASE() _dafny.Int {
  return Companion_Default___.Base()
}
func (_static *CompanionStruct_Default___) IsDigitChar(c _dafny.CodePoint) bool {
  return (Companion_Default___.CharToDigit()).Contains(c)
}
func (_static *CompanionStruct_Default___) OfDigits(digits _dafny.Sequence) _dafny.Sequence {
  var _150___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _150___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if (_dafny.Companion_Sequence_.Equal(digits, _dafny.SeqOf())) {
    return _dafny.Companion_Sequence_.Concatenate(_dafny.SeqOf(), _150___accumulator)
  } else {
    _150___accumulator = _dafny.Companion_Sequence_.Concatenate(_dafny.SeqOf((Companion_Default___.Chars()).Select(((digits).Select(0).(_dafny.Int)).Uint32()).(_dafny.CodePoint)), _150___accumulator)
    var _in51 _dafny.Sequence = (digits).Drop(1)
    _ = _in51
    digits = _in51
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) OfNat(n _dafny.Int) _dafny.Sequence {
  if ((n).Sign() == 0) {
    return _dafny.SeqOf((Companion_Default___.Chars()).Select(0).(_dafny.CodePoint))
  } else {
    return Companion_Default___.OfDigits(Companion_Default___.FromNat(n))
  }
}
func (_static *CompanionStruct_Default___) IsNumberStr(str _dafny.Sequence, minus _dafny.CodePoint) bool {
  return !(!_dafny.Companion_Sequence_.Equal(str, _dafny.SeqOf())) || (((((str).Select(0).(_dafny.CodePoint)) == (minus)) || ((Companion_Default___.CharToDigit()).Contains((str).Select(0).(_dafny.CodePoint)))) && (_dafny.Quantifier(((str).Drop(1)).UniqueElements(), true, func (_forall_var_2 _dafny.CodePoint) bool {
    var _151_c _dafny.CodePoint
    _151_c = interface{}(_forall_var_2).(_dafny.CodePoint)
    return !(_dafny.Companion_Sequence_.Contains((str).Drop(1), _151_c)) || (Companion_Default___.IsDigitChar(_151_c))
  })))
}
func (_static *CompanionStruct_Default___) OfInt(n _dafny.Int, minus _dafny.CodePoint) _dafny.Sequence {
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
    var _152_c _dafny.CodePoint = (str).Select(((_dafny.IntOfUint32((str).Cardinality())).Minus(_dafny.One)).Uint32()).(_dafny.CodePoint)
    _ = _152_c
    return ((Companion_Default___.ToNat((str).Take(((_dafny.IntOfUint32((str).Cardinality())).Minus(_dafny.One)).Uint32()))).Times(Companion_Default___.Base())).Plus((Companion_Default___.CharToDigit()).Get(_152_c).(_dafny.Int))
  }
}
func (_static *CompanionStruct_Default___) ToInt(str _dafny.Sequence, minus _dafny.CodePoint) _dafny.Int {
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
  var _153___accumulator _dafny.Int = _dafny.Zero
  _ = _153___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return (_dafny.Zero).Plus(_153___accumulator)
  } else {
    _153___accumulator = ((Std_Collections_Seq.Companion_Default___.Last(xs).(_dafny.Int)).Times(Std_Arithmetic_Power.Companion_Default___.Pow(Companion_Default___.BASE(), (_dafny.IntOfUint32((xs).Cardinality())).Minus(_dafny.One)))).Plus(_153___accumulator)
    var _in52 _dafny.Sequence = Std_Collections_Seq.Companion_Default___.DropLast(xs)
    _ = _in52
    xs = _in52
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) FromNat(n _dafny.Int) _dafny.Sequence {
  var _154___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _154___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((n).Sign() == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_154___accumulator, _dafny.SeqOf())
  } else {
    _154___accumulator = _dafny.Companion_Sequence_.Concatenate(_154___accumulator, _dafny.SeqOf((n).Modulo(Companion_Default___.BASE())))
    var _in53 _dafny.Int = (n).DivBy(Companion_Default___.BASE())
    _ = _in53
    n = _in53
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) SeqExtend(xs _dafny.Sequence, n _dafny.Int) _dafny.Sequence {
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((xs).Cardinality())).Cmp(n) >= 0) {
    return xs
  } else {
    var _in54 _dafny.Sequence = _dafny.Companion_Sequence_.Concatenate(xs, _dafny.SeqOf(_dafny.Zero))
    _ = _in54
    var _in55 _dafny.Int = n
    _ = _in55
    xs = _in54
    n = _in55
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) SeqExtendMultiple(xs _dafny.Sequence, n _dafny.Int) _dafny.Sequence {
  var _155_newLen _dafny.Int = ((_dafny.IntOfUint32((xs).Cardinality())).Plus(n)).Minus((_dafny.IntOfUint32((xs).Cardinality())).Modulo(n))
  _ = _155_newLen
  return Companion_Default___.SeqExtend(xs, _155_newLen)
}
func (_static *CompanionStruct_Default___) FromNatWithLen(n _dafny.Int, len_ _dafny.Int) _dafny.Sequence {
  return Companion_Default___.SeqExtend(Companion_Default___.FromNat(n), len_)
}
func (_static *CompanionStruct_Default___) SeqZero(len_ _dafny.Int) _dafny.Sequence {
  var _156_xs _dafny.Sequence = Companion_Default___.FromNatWithLen(_dafny.Zero, len_)
  _ = _156_xs
  return _156_xs
}
func (_static *CompanionStruct_Default___) SeqAdd(xs _dafny.Sequence, ys _dafny.Sequence) _dafny.Tuple {
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return _dafny.TupleOf(_dafny.SeqOf(), _dafny.Zero)
  } else {
    var _let_tmp_rhs5 _dafny.Tuple = Companion_Default___.SeqAdd(Std_Collections_Seq.Companion_Default___.DropLast(xs), Std_Collections_Seq.Companion_Default___.DropLast(ys))
    _ = _let_tmp_rhs5
    var _157_zs_k _dafny.Sequence = (*(_let_tmp_rhs5).IndexInt(0)).(_dafny.Sequence)
    _ = _157_zs_k
    var _158_cin _dafny.Int = (*(_let_tmp_rhs5).IndexInt(1)).(_dafny.Int)
    _ = _158_cin
    var _159_sum _dafny.Int = ((Std_Collections_Seq.Companion_Default___.Last(xs).(_dafny.Int)).Plus(Std_Collections_Seq.Companion_Default___.Last(ys).(_dafny.Int))).Plus(_158_cin)
    _ = _159_sum
    var _let_tmp_rhs6 _dafny.Tuple = (func () _dafny.Tuple { if (_159_sum).Cmp(Companion_Default___.BASE()) < 0 { return _dafny.TupleOf(_159_sum, _dafny.Zero) }; return _dafny.TupleOf((_159_sum).Minus(Companion_Default___.BASE()), _dafny.One) })() 
    _ = _let_tmp_rhs6
    var _160_sum__out _dafny.Int = (*(_let_tmp_rhs6).IndexInt(0)).(_dafny.Int)
    _ = _160_sum__out
    var _161_cout _dafny.Int = (*(_let_tmp_rhs6).IndexInt(1)).(_dafny.Int)
    _ = _161_cout
    return _dafny.TupleOf(_dafny.Companion_Sequence_.Concatenate(_157_zs_k, _dafny.SeqOf(_160_sum__out)), _161_cout)
  }
}
func (_static *CompanionStruct_Default___) SeqSub(xs _dafny.Sequence, ys _dafny.Sequence) _dafny.Tuple {
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return _dafny.TupleOf(_dafny.SeqOf(), _dafny.Zero)
  } else {
    var _let_tmp_rhs7 _dafny.Tuple = Companion_Default___.SeqSub(Std_Collections_Seq.Companion_Default___.DropLast(xs), Std_Collections_Seq.Companion_Default___.DropLast(ys))
    _ = _let_tmp_rhs7
    var _162_zs _dafny.Sequence = (*(_let_tmp_rhs7).IndexInt(0)).(_dafny.Sequence)
    _ = _162_zs
    var _163_cin _dafny.Int = (*(_let_tmp_rhs7).IndexInt(1)).(_dafny.Int)
    _ = _163_cin
    var _let_tmp_rhs8 _dafny.Tuple = (func () _dafny.Tuple { if (Std_Collections_Seq.Companion_Default___.Last(xs).(_dafny.Int)).Cmp((Std_Collections_Seq.Companion_Default___.Last(ys).(_dafny.Int)).Plus(_163_cin)) >= 0 { return _dafny.TupleOf(((Std_Collections_Seq.Companion_Default___.Last(xs).(_dafny.Int)).Minus(Std_Collections_Seq.Companion_Default___.Last(ys).(_dafny.Int))).Minus(_163_cin), _dafny.Zero) }; return _dafny.TupleOf((((Companion_Default___.BASE()).Plus(Std_Collections_Seq.Companion_Default___.Last(xs).(_dafny.Int))).Minus(Std_Collections_Seq.Companion_Default___.Last(ys).(_dafny.Int))).Minus(_163_cin), _dafny.One) })() 
    _ = _let_tmp_rhs8
    var _164_diff__out _dafny.Int = (*(_let_tmp_rhs8).IndexInt(0)).(_dafny.Int)
    _ = _164_diff__out
    var _165_cout _dafny.Int = (*(_let_tmp_rhs8).IndexInt(1)).(_dafny.Int)
    _ = _165_cout
    return _dafny.TupleOf(_dafny.Companion_Sequence_.Concatenate(_162_zs, _dafny.SeqOf(_164_diff__out)), _165_cout)
  }
}
func (_static *CompanionStruct_Default___) DIGITS() _dafny.Sequence {
  return _dafny.UnicodeSeqOfUtf8Bytes("0123456789")
}
func (_static *CompanionStruct_Default___) Chars() _dafny.Sequence {
  return Companion_Default___.DIGITS()
}
func (_static *CompanionStruct_Default___) Base() _dafny.Int {
  return _dafny.IntOfUint32((Companion_Default___.Chars()).Cardinality())
}
func (_static *CompanionStruct_Default___) CharToDigit() _dafny.Map {
  return _dafny.NewMapBuilder().ToMap().UpdateUnsafe(_dafny.CodePoint('0'), _dafny.Zero).UpdateUnsafe(_dafny.CodePoint('1'), _dafny.One).UpdateUnsafe(_dafny.CodePoint('2'), _dafny.IntOfInt64(2)).UpdateUnsafe(_dafny.CodePoint('3'), _dafny.IntOfInt64(3)).UpdateUnsafe(_dafny.CodePoint('4'), _dafny.IntOfInt64(4)).UpdateUnsafe(_dafny.CodePoint('5'), _dafny.IntOfInt64(5)).UpdateUnsafe(_dafny.CodePoint('6'), _dafny.IntOfInt64(6)).UpdateUnsafe(_dafny.CodePoint('7'), _dafny.IntOfInt64(7)).UpdateUnsafe(_dafny.CodePoint('8'), _dafny.IntOfInt64(8)).UpdateUnsafe(_dafny.CodePoint('9'), _dafny.IntOfInt64(9))
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
  return "Std_Strings_DecimalConversion.CharSeq"
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
  return "Std_Strings_DecimalConversion.CharSeq"
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
  return "Std_Strings_DecimalConversion.Digit"
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
  return "Std_Strings_DecimalConversion.Digit"
}
