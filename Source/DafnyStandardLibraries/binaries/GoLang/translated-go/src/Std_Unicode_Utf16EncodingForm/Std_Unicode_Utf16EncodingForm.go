// Package Std_Unicode_Utf16EncodingForm
// Dafny module Std_Unicode_Utf16EncodingForm compiled into Go

package Std_Unicode_Utf16EncodingForm

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
  return "Std_Unicode_Utf16EncodingForm.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) IsMinimalWellFormedCodeUnitSubsequence(s _dafny.Sequence) bool {
  if ((_dafny.IntOfUint32((s).Cardinality())).Cmp(_dafny.One) == 0) {
    return Companion_Default___.IsWellFormedSingleCodeUnitSequence(s)
  } else if ((_dafny.IntOfUint32((s).Cardinality())).Cmp(_dafny.IntOfInt64(2)) == 0) {
    var _231_b bool = Companion_Default___.IsWellFormedDoubleCodeUnitSequence(s)
    _ = _231_b
    return _231_b
  } else {
    return false
  }
}
func (_static *CompanionStruct_Default___) IsWellFormedSingleCodeUnitSequence(s _dafny.Sequence) bool {
  var _232_firstWord uint16 = (s).Select(0).(uint16)
  _ = _232_firstWord
  return (((uint16(0)) <= (_232_firstWord)) && ((_232_firstWord) <= (uint16(55295)))) || (((uint16(57344)) <= (_232_firstWord)) && ((_232_firstWord) <= (uint16(65535))))
}
func (_static *CompanionStruct_Default___) IsWellFormedDoubleCodeUnitSequence(s _dafny.Sequence) bool {
  var _233_firstWord uint16 = (s).Select(0).(uint16)
  _ = _233_firstWord
  var _234_secondWord uint16 = (s).Select(1).(uint16)
  _ = _234_secondWord
  return (((uint16(55296)) <= (_233_firstWord)) && ((_233_firstWord) <= (uint16(56319)))) && (((uint16(56320)) <= (_234_secondWord)) && ((_234_secondWord) <= (uint16(57343))))
}
func (_static *CompanionStruct_Default___) SplitPrefixMinimalWellFormedCodeUnitSubsequence(s _dafny.Sequence) Std_Wrappers.Option {
  if (((_dafny.IntOfUint32((s).Cardinality())).Cmp(_dafny.One) >= 0) && (Companion_Default___.IsWellFormedSingleCodeUnitSequence((s).Take(1)))) {
    return Std_Wrappers.Companion_Option_.Create_Some_((s).Take(1))
  } else if (((_dafny.IntOfUint32((s).Cardinality())).Cmp(_dafny.IntOfInt64(2)) >= 0) && (Companion_Default___.IsWellFormedDoubleCodeUnitSequence((s).Take(2)))) {
    return Std_Wrappers.Companion_Option_.Create_Some_((s).Take(2))
  } else {
    return Std_Wrappers.Companion_Option_.Create_None_()
  }
}
func (_static *CompanionStruct_Default___) EncodeScalarValue(v uint32) _dafny.Sequence {
  if ((((uint32(0)) <= (v)) && ((v) <= (uint32(55295)))) || (((uint32(57344)) <= (v)) && ((v) <= (uint32(65535))))) {
    return Companion_Default___.EncodeScalarValueSingleWord(v)
  } else {
    return Companion_Default___.EncodeScalarValueDoubleWord(v)
  }
}
func (_static *CompanionStruct_Default___) EncodeScalarValueSingleWord(v uint32) _dafny.Sequence {
  var _235_firstWord uint16 = uint16(v)
  _ = _235_firstWord
  return _dafny.SeqOf(_235_firstWord)
}
func (_static *CompanionStruct_Default___) EncodeScalarValueDoubleWord(v uint32) _dafny.Sequence {
  var _236_x2 uint16 = uint16((v) & (uint32(1023)))
  _ = _236_x2
  var _237_x1 uint8 = uint8(((v) & (uint32(64512))) >> (uint8(10)))
  _ = _237_x1
  var _238_u uint8 = uint8(((v) & (uint32(2031616))) >> (uint8(16)))
  _ = _238_u
  var _239_w uint8 = uint8((((_238_u) - (func () uint8 { return  (uint8(1)) })()) & 0x1F))
  _ = _239_w
  var _240_firstWord uint16 = ((uint16(55296)) | ((uint16(_239_w)) << (uint8(6)))) | (uint16(_237_x1))
  _ = _240_firstWord
  var _241_secondWord uint16 = (uint16(56320)) | (uint16(_236_x2))
  _ = _241_secondWord
  return _dafny.SeqOf(_240_firstWord, _241_secondWord)
}
func (_static *CompanionStruct_Default___) DecodeMinimalWellFormedCodeUnitSubsequence(m _dafny.Sequence) uint32 {
  if ((_dafny.IntOfUint32((m).Cardinality())).Cmp(_dafny.One) == 0) {
    return Companion_Default___.DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m)
  } else {
    return Companion_Default___.DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m)
  }
}
func (_static *CompanionStruct_Default___) DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m _dafny.Sequence) uint32 {
  var _242_firstWord uint16 = (m).Select(0).(uint16)
  _ = _242_firstWord
  var _243_x uint16 = (_242_firstWord)
  _ = _243_x
  return uint32(_243_x)
}
func (_static *CompanionStruct_Default___) DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m _dafny.Sequence) uint32 {
  var _244_firstWord uint16 = (m).Select(0).(uint16)
  _ = _244_firstWord
  var _245_secondWord uint16 = (m).Select(1).(uint16)
  _ = _245_secondWord
  var _246_x2 uint32 = uint32((_245_secondWord) & (uint16(1023)))
  _ = _246_x2
  var _247_x1 uint32 = uint32((_244_firstWord) & (uint16(63)))
  _ = _247_x1
  var _248_w uint32 = uint32(((_244_firstWord) & (uint16(960))) >> (uint8(6)))
  _ = _248_w
  var _249_u uint32 = ((((_248_w) + (uint32(1))) & 0xFFFFFF))
  _ = _249_u
  var _250_v uint32 = (((((_249_u) << (uint8(16))) & 0xFFFFFF)) | ((((_247_x1) << (uint8(10))) & 0xFFFFFF))) | ((_246_x2))
  _ = _250_v
  return _250_v
}
func (_static *CompanionStruct_Default___) PartitionCodeUnitSequenceChecked(s _dafny.Sequence) Std_Wrappers.Option {
  var maybeParts Std_Wrappers.Option = Std_Wrappers.Companion_Option_.Default()
  _ = maybeParts
  if (_dafny.Companion_Sequence_.Equal(s, _dafny.SeqOf())) {
    maybeParts = Std_Wrappers.Companion_Option_.Create_Some_(_dafny.SeqOf())
    return maybeParts
  }
  var _251_result _dafny.Sequence
  _ = _251_result
  _251_result = _dafny.SeqOf()
  var _252_rest _dafny.Sequence
  _ = _252_rest
  _252_rest = s
  for (_dafny.IntOfUint32((_252_rest).Cardinality())).Sign() == 1 {
    var _253_prefix _dafny.Sequence
    _ = _253_prefix
    var _254_valueOrError0 Std_Wrappers.Option = Std_Wrappers.Companion_Option_.Default()
    _ = _254_valueOrError0
    _254_valueOrError0 = Companion_Default___.SplitPrefixMinimalWellFormedCodeUnitSubsequence(_252_rest)
    if ((_254_valueOrError0).IsFailure()) {
      maybeParts = (_254_valueOrError0).PropagateFailure()
      return maybeParts
    }
    _253_prefix = (_254_valueOrError0).Extract().(_dafny.Sequence)
    _251_result = _dafny.Companion_Sequence_.Concatenate(_251_result, _dafny.SeqOf(_253_prefix))
    _252_rest = (_252_rest).Drop((_dafny.IntOfUint32((_253_prefix).Cardinality())).Uint32())
  }
  maybeParts = Std_Wrappers.Companion_Option_.Create_Some_(_251_result)
  return maybeParts
  return maybeParts
}
func (_static *CompanionStruct_Default___) PartitionCodeUnitSequence(s _dafny.Sequence) _dafny.Sequence {
  return (Companion_Default___.PartitionCodeUnitSequenceChecked(s)).Extract().(_dafny.Sequence)
}
func (_static *CompanionStruct_Default___) IsWellFormedCodeUnitSequence(s _dafny.Sequence) bool {
  return (Companion_Default___.PartitionCodeUnitSequenceChecked(s)).Is_Some()
}
func (_static *CompanionStruct_Default___) EncodeScalarSequence(vs _dafny.Sequence) _dafny.Sequence {
  var s _dafny.Sequence = Companion_WellFormedCodeUnitSeq_.Witness()
  _ = s
  s = _dafny.SeqOf()
  var _lo1 _dafny.Int = _dafny.Zero
  _ = _lo1
  for _255_i := _dafny.IntOfUint32((vs).Cardinality()); _lo1.Cmp(_255_i) < 0;  {
    _255_i = _255_i.Minus(_dafny.One)
    var _256_next _dafny.Sequence
    _ = _256_next
    _256_next = Companion_Default___.EncodeScalarValue((vs).Select((_255_i).Uint32()).(uint32))
    s = _dafny.Companion_Sequence_.Concatenate(_256_next, s)
  }
  return s
}
func (_static *CompanionStruct_Default___) DecodeCodeUnitSequence(s _dafny.Sequence) _dafny.Sequence {
  var _257_parts _dafny.Sequence = Companion_Default___.PartitionCodeUnitSequence(s)
  _ = _257_parts
  var _258_vs _dafny.Sequence = Std_Collections_Seq.Companion_Default___.Map(func (coer8 func (_dafny.Sequence) uint32) func (interface{}) interface{} {
    return func (arg10 interface{}) interface{} {
      return coer8(arg10.(_dafny.Sequence))
    }
  }(Companion_Default___.DecodeMinimalWellFormedCodeUnitSubsequence), _257_parts)
  _ = _258_vs
  return _258_vs
}
func (_static *CompanionStruct_Default___) DecodeCodeUnitSequenceChecked(s _dafny.Sequence) Std_Wrappers.Option {
  var maybeVs Std_Wrappers.Option = Std_Wrappers.Companion_Option_.Default()
  _ = maybeVs
  var _259_maybeParts Std_Wrappers.Option
  _ = _259_maybeParts
  _259_maybeParts = Companion_Default___.PartitionCodeUnitSequenceChecked(s)
  if ((_259_maybeParts).Is_None()) {
    maybeVs = Std_Wrappers.Companion_Option_.Create_None_()
    return maybeVs
  }
  var _260_parts _dafny.Sequence
  _ = _260_parts
  _260_parts = (_259_maybeParts).Dtor_value().(_dafny.Sequence)
  var _261_vs _dafny.Sequence
  _ = _261_vs
  _261_vs = Std_Collections_Seq.Companion_Default___.Map(func (coer9 func (_dafny.Sequence) uint32) func (interface{}) interface{} {
    return func (arg11 interface{}) interface{} {
      return coer9(arg11.(_dafny.Sequence))
    }
  }(Companion_Default___.DecodeMinimalWellFormedCodeUnitSubsequence), _260_parts)
  maybeVs = Std_Wrappers.Companion_Option_.Create_Some_(_261_vs)
  return maybeVs
  return maybeVs
}
// End of class Default__

// Definition of class WellFormedCodeUnitSeq
type WellFormedCodeUnitSeq struct {
}

func New_WellFormedCodeUnitSeq_() *WellFormedCodeUnitSeq {
  _this := WellFormedCodeUnitSeq{}

  return &_this
}

type CompanionStruct_WellFormedCodeUnitSeq_ struct {
}
var Companion_WellFormedCodeUnitSeq_ = CompanionStruct_WellFormedCodeUnitSeq_ {
}

func (*WellFormedCodeUnitSeq) String() string {
  return "Std_Unicode_Utf16EncodingForm.WellFormedCodeUnitSeq"
}
func (_this *CompanionStruct_WellFormedCodeUnitSeq_) Witness() _dafny.Sequence {
  return _dafny.SeqOf()
}
// End of class WellFormedCodeUnitSeq

func Type_WellFormedCodeUnitSeq_() _dafny.TypeDescriptor {
  return type_WellFormedCodeUnitSeq_{}
}

type type_WellFormedCodeUnitSeq_ struct {
}

func (_this type_WellFormedCodeUnitSeq_) Default() interface{} {
  return Companion_WellFormedCodeUnitSeq_.Witness()
}

func (_this type_WellFormedCodeUnitSeq_) String() string {
  return "Std_Unicode_Utf16EncodingForm.WellFormedCodeUnitSeq"
}

// Definition of class MinimalWellFormedCodeUnitSeq
type MinimalWellFormedCodeUnitSeq struct {
}

func New_MinimalWellFormedCodeUnitSeq_() *MinimalWellFormedCodeUnitSeq {
  _this := MinimalWellFormedCodeUnitSeq{}

  return &_this
}

type CompanionStruct_MinimalWellFormedCodeUnitSeq_ struct {
}
var Companion_MinimalWellFormedCodeUnitSeq_ = CompanionStruct_MinimalWellFormedCodeUnitSeq_ {
}

func (*MinimalWellFormedCodeUnitSeq) String() string {
  return "Std_Unicode_Utf16EncodingForm.MinimalWellFormedCodeUnitSeq"
}
// End of class MinimalWellFormedCodeUnitSeq

func Type_MinimalWellFormedCodeUnitSeq_() _dafny.TypeDescriptor {
  return type_MinimalWellFormedCodeUnitSeq_{}
}

type type_MinimalWellFormedCodeUnitSeq_ struct {
}

func (_this type_MinimalWellFormedCodeUnitSeq_) Default() interface{} {
  return _dafny.EmptySeq
}

func (_this type_MinimalWellFormedCodeUnitSeq_) String() string {
  return "Std_Unicode_Utf16EncodingForm.MinimalWellFormedCodeUnitSeq"
}
