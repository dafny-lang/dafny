// Package Std_Unicode_Utf8EncodingForm
// Dafny module Std_Unicode_Utf8EncodingForm compiled into Go

package Std_Unicode_Utf8EncodingForm

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
  return "Std_Unicode_Utf8EncodingForm.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) IsMinimalWellFormedCodeUnitSubsequence(s _dafny.Sequence) bool {
  if ((_dafny.IntOfUint32((s).Cardinality())).Cmp(_dafny.One) == 0) {
    var _172_b bool = Companion_Default___.IsWellFormedSingleCodeUnitSequence(s)
    _ = _172_b
    return _172_b
  } else if ((_dafny.IntOfUint32((s).Cardinality())).Cmp(_dafny.IntOfInt64(2)) == 0) {
    var _173_b bool = Companion_Default___.IsWellFormedDoubleCodeUnitSequence(s)
    _ = _173_b
    return _173_b
  } else if ((_dafny.IntOfUint32((s).Cardinality())).Cmp(_dafny.IntOfInt64(3)) == 0) {
    var _174_b bool = Companion_Default___.IsWellFormedTripleCodeUnitSequence(s)
    _ = _174_b
    return _174_b
  } else if ((_dafny.IntOfUint32((s).Cardinality())).Cmp(_dafny.IntOfInt64(4)) == 0) {
    var _175_b bool = Companion_Default___.IsWellFormedQuadrupleCodeUnitSequence(s)
    _ = _175_b
    return _175_b
  } else {
    return false
  }
}
func (_static *CompanionStruct_Default___) IsWellFormedSingleCodeUnitSequence(s _dafny.Sequence) bool {
  var _176_firstByte uint8 = (s).Select(0).(uint8)
  _ = _176_firstByte
  return (true) && (((uint8(0)) <= (_176_firstByte)) && ((_176_firstByte) <= (uint8(127))))
}
func (_static *CompanionStruct_Default___) IsWellFormedDoubleCodeUnitSequence(s _dafny.Sequence) bool {
  var _177_firstByte uint8 = (s).Select(0).(uint8)
  _ = _177_firstByte
  var _178_secondByte uint8 = (s).Select(1).(uint8)
  _ = _178_secondByte
  return (((uint8(194)) <= (_177_firstByte)) && ((_177_firstByte) <= (uint8(223)))) && (((uint8(128)) <= (_178_secondByte)) && ((_178_secondByte) <= (uint8(191))))
}
func (_static *CompanionStruct_Default___) IsWellFormedTripleCodeUnitSequence(s _dafny.Sequence) bool {
  var _179_firstByte uint8 = (s).Select(0).(uint8)
  _ = _179_firstByte
  var _180_secondByte uint8 = (s).Select(1).(uint8)
  _ = _180_secondByte
  var _181_thirdByte uint8 = (s).Select(2).(uint8)
  _ = _181_thirdByte
  return ((((((_179_firstByte) == (uint8(224))) && (((uint8(160)) <= (_180_secondByte)) && ((_180_secondByte) <= (uint8(191))))) || ((((uint8(225)) <= (_179_firstByte)) && ((_179_firstByte) <= (uint8(236)))) && (((uint8(128)) <= (_180_secondByte)) && ((_180_secondByte) <= (uint8(191)))))) || (((_179_firstByte) == (uint8(237))) && (((uint8(128)) <= (_180_secondByte)) && ((_180_secondByte) <= (uint8(159)))))) || ((((uint8(238)) <= (_179_firstByte)) && ((_179_firstByte) <= (uint8(239)))) && (((uint8(128)) <= (_180_secondByte)) && ((_180_secondByte) <= (uint8(191)))))) && (((uint8(128)) <= (_181_thirdByte)) && ((_181_thirdByte) <= (uint8(191))))
}
func (_static *CompanionStruct_Default___) IsWellFormedQuadrupleCodeUnitSequence(s _dafny.Sequence) bool {
  var _182_firstByte uint8 = (s).Select(0).(uint8)
  _ = _182_firstByte
  var _183_secondByte uint8 = (s).Select(1).(uint8)
  _ = _183_secondByte
  var _184_thirdByte uint8 = (s).Select(2).(uint8)
  _ = _184_thirdByte
  var _185_fourthByte uint8 = (s).Select(3).(uint8)
  _ = _185_fourthByte
  return ((((((_182_firstByte) == (uint8(240))) && (((uint8(144)) <= (_183_secondByte)) && ((_183_secondByte) <= (uint8(191))))) || ((((uint8(241)) <= (_182_firstByte)) && ((_182_firstByte) <= (uint8(243)))) && (((uint8(128)) <= (_183_secondByte)) && ((_183_secondByte) <= (uint8(191)))))) || (((_182_firstByte) == (uint8(244))) && (((uint8(128)) <= (_183_secondByte)) && ((_183_secondByte) <= (uint8(143)))))) && (((uint8(128)) <= (_184_thirdByte)) && ((_184_thirdByte) <= (uint8(191))))) && (((uint8(128)) <= (_185_fourthByte)) && ((_185_fourthByte) <= (uint8(191))))
}
func (_static *CompanionStruct_Default___) SplitPrefixMinimalWellFormedCodeUnitSubsequence(s _dafny.Sequence) Std_Wrappers.Option {
  if (((_dafny.IntOfUint32((s).Cardinality())).Cmp(_dafny.One) >= 0) && (Companion_Default___.IsWellFormedSingleCodeUnitSequence((s).Take(1)))) {
    return Std_Wrappers.Companion_Option_.Create_Some_((s).Take(1))
  } else if (((_dafny.IntOfUint32((s).Cardinality())).Cmp(_dafny.IntOfInt64(2)) >= 0) && (Companion_Default___.IsWellFormedDoubleCodeUnitSequence((s).Take(2)))) {
    return Std_Wrappers.Companion_Option_.Create_Some_((s).Take(2))
  } else if (((_dafny.IntOfUint32((s).Cardinality())).Cmp(_dafny.IntOfInt64(3)) >= 0) && (Companion_Default___.IsWellFormedTripleCodeUnitSequence((s).Take(3)))) {
    return Std_Wrappers.Companion_Option_.Create_Some_((s).Take(3))
  } else if (((_dafny.IntOfUint32((s).Cardinality())).Cmp(_dafny.IntOfInt64(4)) >= 0) && (Companion_Default___.IsWellFormedQuadrupleCodeUnitSequence((s).Take(4)))) {
    return Std_Wrappers.Companion_Option_.Create_Some_((s).Take(4))
  } else {
    return Std_Wrappers.Companion_Option_.Create_None_()
  }
}
func (_static *CompanionStruct_Default___) EncodeScalarValue(v uint32) _dafny.Sequence {
  if ((v) <= (uint32(127))) {
    return Companion_Default___.EncodeScalarValueSingleByte(v)
  } else if ((v) <= (uint32(2047))) {
    return Companion_Default___.EncodeScalarValueDoubleByte(v)
  } else if ((v) <= (uint32(65535))) {
    return Companion_Default___.EncodeScalarValueTripleByte(v)
  } else {
    return Companion_Default___.EncodeScalarValueQuadrupleByte(v)
  }
}
func (_static *CompanionStruct_Default___) EncodeScalarValueSingleByte(v uint32) _dafny.Sequence {
  var _186_x uint8 = uint8((v) & (uint32(127)))
  _ = _186_x
  var _187_firstByte uint8 = uint8(_186_x)
  _ = _187_firstByte
  return _dafny.SeqOf(_187_firstByte)
}
func (_static *CompanionStruct_Default___) EncodeScalarValueDoubleByte(v uint32) _dafny.Sequence {
  var _188_x uint8 = uint8((v) & (uint32(63)))
  _ = _188_x
  var _189_y uint8 = uint8(((v) & (uint32(1984))) >> (uint8(6)))
  _ = _189_y
  var _190_firstByte uint8 = (uint8(192)) | (uint8(_189_y))
  _ = _190_firstByte
  var _191_secondByte uint8 = (uint8(128)) | (uint8(_188_x))
  _ = _191_secondByte
  return _dafny.SeqOf(_190_firstByte, _191_secondByte)
}
func (_static *CompanionStruct_Default___) EncodeScalarValueTripleByte(v uint32) _dafny.Sequence {
  var _192_x uint8 = uint8((v) & (uint32(63)))
  _ = _192_x
  var _193_y uint8 = uint8(((v) & (uint32(4032))) >> (uint8(6)))
  _ = _193_y
  var _194_z uint8 = uint8(((v) & (uint32(61440))) >> (uint8(12)))
  _ = _194_z
  var _195_firstByte uint8 = (uint8(224)) | (uint8(_194_z))
  _ = _195_firstByte
  var _196_secondByte uint8 = (uint8(128)) | (uint8(_193_y))
  _ = _196_secondByte
  var _197_thirdByte uint8 = (uint8(128)) | (uint8(_192_x))
  _ = _197_thirdByte
  return _dafny.SeqOf(_195_firstByte, _196_secondByte, _197_thirdByte)
}
func (_static *CompanionStruct_Default___) EncodeScalarValueQuadrupleByte(v uint32) _dafny.Sequence {
  var _198_x uint8 = uint8((v) & (uint32(63)))
  _ = _198_x
  var _199_y uint8 = uint8(((v) & (uint32(4032))) >> (uint8(6)))
  _ = _199_y
  var _200_z uint8 = uint8(((v) & (uint32(61440))) >> (uint8(12)))
  _ = _200_z
  var _201_u2 uint8 = uint8(((v) & (uint32(196608))) >> (uint8(16)))
  _ = _201_u2
  var _202_u1 uint8 = uint8(((v) & (uint32(1835008))) >> (uint8(18)))
  _ = _202_u1
  var _203_firstByte uint8 = (uint8(240)) | (uint8(_202_u1))
  _ = _203_firstByte
  var _204_secondByte uint8 = ((uint8(128)) | ((uint8(_201_u2)) << (uint8(4)))) | (uint8(_200_z))
  _ = _204_secondByte
  var _205_thirdByte uint8 = (uint8(128)) | (uint8(_199_y))
  _ = _205_thirdByte
  var _206_fourthByte uint8 = (uint8(128)) | (uint8(_198_x))
  _ = _206_fourthByte
  return _dafny.SeqOf(_203_firstByte, _204_secondByte, _205_thirdByte, _206_fourthByte)
}
func (_static *CompanionStruct_Default___) DecodeMinimalWellFormedCodeUnitSubsequence(m _dafny.Sequence) uint32 {
  if ((_dafny.IntOfUint32((m).Cardinality())).Cmp(_dafny.One) == 0) {
    return Companion_Default___.DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(m)
  } else if ((_dafny.IntOfUint32((m).Cardinality())).Cmp(_dafny.IntOfInt64(2)) == 0) {
    return Companion_Default___.DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m)
  } else if ((_dafny.IntOfUint32((m).Cardinality())).Cmp(_dafny.IntOfInt64(3)) == 0) {
    return Companion_Default___.DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m)
  } else {
    return Companion_Default___.DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(m)
  }
}
func (_static *CompanionStruct_Default___) DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(m _dafny.Sequence) uint32 {
  var _207_firstByte uint8 = (m).Select(0).(uint8)
  _ = _207_firstByte
  var _208_x uint8 = uint8(_207_firstByte)
  _ = _208_x
  return uint32(_208_x)
}
func (_static *CompanionStruct_Default___) DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m _dafny.Sequence) uint32 {
  var _209_firstByte uint8 = (m).Select(0).(uint8)
  _ = _209_firstByte
  var _210_secondByte uint8 = (m).Select(1).(uint8)
  _ = _210_secondByte
  var _211_y uint32 = uint32((_209_firstByte) & (uint8(31)))
  _ = _211_y
  var _212_x uint32 = uint32((_210_secondByte) & (uint8(63)))
  _ = _212_x
  return ((((_211_y) << (uint8(6))) & 0xFFFFFF)) | ((_212_x))
}
func (_static *CompanionStruct_Default___) DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m _dafny.Sequence) uint32 {
  var _213_firstByte uint8 = (m).Select(0).(uint8)
  _ = _213_firstByte
  var _214_secondByte uint8 = (m).Select(1).(uint8)
  _ = _214_secondByte
  var _215_thirdByte uint8 = (m).Select(2).(uint8)
  _ = _215_thirdByte
  var _216_z uint32 = uint32((_213_firstByte) & (uint8(15)))
  _ = _216_z
  var _217_y uint32 = uint32((_214_secondByte) & (uint8(63)))
  _ = _217_y
  var _218_x uint32 = uint32((_215_thirdByte) & (uint8(63)))
  _ = _218_x
  return (((((_216_z) << (uint8(12))) & 0xFFFFFF)) | ((((_217_y) << (uint8(6))) & 0xFFFFFF))) | ((_218_x))
}
func (_static *CompanionStruct_Default___) DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(m _dafny.Sequence) uint32 {
  var _219_firstByte uint8 = (m).Select(0).(uint8)
  _ = _219_firstByte
  var _220_secondByte uint8 = (m).Select(1).(uint8)
  _ = _220_secondByte
  var _221_thirdByte uint8 = (m).Select(2).(uint8)
  _ = _221_thirdByte
  var _222_fourthByte uint8 = (m).Select(3).(uint8)
  _ = _222_fourthByte
  var _223_u1 uint32 = uint32((_219_firstByte) & (uint8(7)))
  _ = _223_u1
  var _224_u2 uint32 = uint32(((_220_secondByte) & (uint8(48))) >> (uint8(4)))
  _ = _224_u2
  var _225_z uint32 = uint32((_220_secondByte) & (uint8(15)))
  _ = _225_z
  var _226_y uint32 = uint32((_221_thirdByte) & (uint8(63)))
  _ = _226_y
  var _227_x uint32 = uint32((_222_fourthByte) & (uint8(63)))
  _ = _227_x
  return (((((((_223_u1) << (uint8(18))) & 0xFFFFFF)) | ((((_224_u2) << (uint8(16))) & 0xFFFFFF))) | ((((_225_z) << (uint8(12))) & 0xFFFFFF))) | ((((_226_y) << (uint8(6))) & 0xFFFFFF))) | ((_227_x))
}
func (_static *CompanionStruct_Default___) PartitionCodeUnitSequenceChecked(s _dafny.Sequence) Std_Wrappers.Option {
  var maybeParts Std_Wrappers.Option = Std_Wrappers.Companion_Option_.Default()
  _ = maybeParts
  if (_dafny.Companion_Sequence_.Equal(s, _dafny.SeqOf())) {
    maybeParts = Std_Wrappers.Companion_Option_.Create_Some_(_dafny.SeqOf())
    return maybeParts
  }
  var _228_result _dafny.Sequence
  _ = _228_result
  _228_result = _dafny.SeqOf()
  var _229_rest _dafny.Sequence
  _ = _229_rest
  _229_rest = s
  for (_dafny.IntOfUint32((_229_rest).Cardinality())).Sign() == 1 {
    var _230_prefix _dafny.Sequence
    _ = _230_prefix
    var _231_valueOrError0 Std_Wrappers.Option = Std_Wrappers.Companion_Option_.Default()
    _ = _231_valueOrError0
    _231_valueOrError0 = Companion_Default___.SplitPrefixMinimalWellFormedCodeUnitSubsequence(_229_rest)
    if ((_231_valueOrError0).IsFailure()) {
      maybeParts = (_231_valueOrError0).PropagateFailure()
      return maybeParts
    }
    _230_prefix = (_231_valueOrError0).Extract().(_dafny.Sequence)
    _228_result = _dafny.Companion_Sequence_.Concatenate(_228_result, _dafny.SeqOf(_230_prefix))
    _229_rest = (_229_rest).Drop((_dafny.IntOfUint32((_230_prefix).Cardinality())).Uint32())
  }
  maybeParts = Std_Wrappers.Companion_Option_.Create_Some_(_228_result)
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
  var _lo0 _dafny.Int = _dafny.Zero
  _ = _lo0
  for _232_i := _dafny.IntOfUint32((vs).Cardinality()); _lo0.Cmp(_232_i) < 0;  {
    _232_i = _232_i.Minus(_dafny.One)
    var _233_next _dafny.Sequence
    _ = _233_next
    _233_next = Companion_Default___.EncodeScalarValue((vs).Select((_232_i).Uint32()).(uint32))
    s = _dafny.Companion_Sequence_.Concatenate(_233_next, s)
  }
  return s
}
func (_static *CompanionStruct_Default___) DecodeCodeUnitSequence(s _dafny.Sequence) _dafny.Sequence {
  var _234_parts _dafny.Sequence = Companion_Default___.PartitionCodeUnitSequence(s)
  _ = _234_parts
  var _235_vs _dafny.Sequence = Std_Collections_Seq.Companion_Default___.Map(func (coer8 func (_dafny.Sequence) uint32) func (interface{}) interface{} {
    return func (arg10 interface{}) interface{} {
      return coer8(arg10.(_dafny.Sequence))
    }
  }(Companion_Default___.DecodeMinimalWellFormedCodeUnitSubsequence), _234_parts)
  _ = _235_vs
  return _235_vs
}
func (_static *CompanionStruct_Default___) DecodeCodeUnitSequenceChecked(s _dafny.Sequence) Std_Wrappers.Option {
  var maybeVs Std_Wrappers.Option = Std_Wrappers.Companion_Option_.Default()
  _ = maybeVs
  var _236_maybeParts Std_Wrappers.Option
  _ = _236_maybeParts
  _236_maybeParts = Companion_Default___.PartitionCodeUnitSequenceChecked(s)
  if ((_236_maybeParts).Is_None()) {
    maybeVs = Std_Wrappers.Companion_Option_.Create_None_()
    return maybeVs
  }
  var _237_parts _dafny.Sequence
  _ = _237_parts
  _237_parts = (_236_maybeParts).Dtor_value().(_dafny.Sequence)
  var _238_vs _dafny.Sequence
  _ = _238_vs
  _238_vs = Std_Collections_Seq.Companion_Default___.Map(func (coer9 func (_dafny.Sequence) uint32) func (interface{}) interface{} {
    return func (arg11 interface{}) interface{} {
      return coer9(arg11.(_dafny.Sequence))
    }
  }(Companion_Default___.DecodeMinimalWellFormedCodeUnitSubsequence), _237_parts)
  maybeVs = Std_Wrappers.Companion_Option_.Create_Some_(_238_vs)
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
  return "Std_Unicode_Utf8EncodingForm.WellFormedCodeUnitSeq"
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
  return "Std_Unicode_Utf8EncodingForm.WellFormedCodeUnitSeq"
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
  return "Std_Unicode_Utf8EncodingForm.MinimalWellFormedCodeUnitSeq"
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
  return "Std_Unicode_Utf8EncodingForm.MinimalWellFormedCodeUnitSeq"
}
