// Package Std_Unicode_Utf8EncodingForm
// Dafny module Std_Unicode_Utf8EncodingForm compiled into Go

package Std_Unicode_Utf8EncodingForm

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
    var _164_b bool = Companion_Default___.IsWellFormedSingleCodeUnitSequence(s)
    _ = _164_b
    return _164_b
  } else if ((_dafny.IntOfUint32((s).Cardinality())).Cmp(_dafny.IntOfInt64(2)) == 0) {
    var _165_b bool = Companion_Default___.IsWellFormedDoubleCodeUnitSequence(s)
    _ = _165_b
    return _165_b
  } else if ((_dafny.IntOfUint32((s).Cardinality())).Cmp(_dafny.IntOfInt64(3)) == 0) {
    var _166_b bool = Companion_Default___.IsWellFormedTripleCodeUnitSequence(s)
    _ = _166_b
    return _166_b
  } else if ((_dafny.IntOfUint32((s).Cardinality())).Cmp(_dafny.IntOfInt64(4)) == 0) {
    var _167_b bool = Companion_Default___.IsWellFormedQuadrupleCodeUnitSequence(s)
    _ = _167_b
    return _167_b
  } else {
    return false
  }
}
func (_static *CompanionStruct_Default___) IsWellFormedSingleCodeUnitSequence(s _dafny.Sequence) bool {
  var _168_firstByte uint8 = (s).Select(0).(uint8)
  _ = _168_firstByte
  return (true) && (((uint8(0)) <= (_168_firstByte)) && ((_168_firstByte) <= (uint8(127))))
}
func (_static *CompanionStruct_Default___) IsWellFormedDoubleCodeUnitSequence(s _dafny.Sequence) bool {
  var _169_firstByte uint8 = (s).Select(0).(uint8)
  _ = _169_firstByte
  var _170_secondByte uint8 = (s).Select(1).(uint8)
  _ = _170_secondByte
  return (((uint8(194)) <= (_169_firstByte)) && ((_169_firstByte) <= (uint8(223)))) && (((uint8(128)) <= (_170_secondByte)) && ((_170_secondByte) <= (uint8(191))))
}
func (_static *CompanionStruct_Default___) IsWellFormedTripleCodeUnitSequence(s _dafny.Sequence) bool {
  var _171_firstByte uint8 = (s).Select(0).(uint8)
  _ = _171_firstByte
  var _172_secondByte uint8 = (s).Select(1).(uint8)
  _ = _172_secondByte
  var _173_thirdByte uint8 = (s).Select(2).(uint8)
  _ = _173_thirdByte
  return ((((((_171_firstByte) == (uint8(224))) && (((uint8(160)) <= (_172_secondByte)) && ((_172_secondByte) <= (uint8(191))))) || ((((uint8(225)) <= (_171_firstByte)) && ((_171_firstByte) <= (uint8(236)))) && (((uint8(128)) <= (_172_secondByte)) && ((_172_secondByte) <= (uint8(191)))))) || (((_171_firstByte) == (uint8(237))) && (((uint8(128)) <= (_172_secondByte)) && ((_172_secondByte) <= (uint8(159)))))) || ((((uint8(238)) <= (_171_firstByte)) && ((_171_firstByte) <= (uint8(239)))) && (((uint8(128)) <= (_172_secondByte)) && ((_172_secondByte) <= (uint8(191)))))) && (((uint8(128)) <= (_173_thirdByte)) && ((_173_thirdByte) <= (uint8(191))))
}
func (_static *CompanionStruct_Default___) IsWellFormedQuadrupleCodeUnitSequence(s _dafny.Sequence) bool {
  var _174_firstByte uint8 = (s).Select(0).(uint8)
  _ = _174_firstByte
  var _175_secondByte uint8 = (s).Select(1).(uint8)
  _ = _175_secondByte
  var _176_thirdByte uint8 = (s).Select(2).(uint8)
  _ = _176_thirdByte
  var _177_fourthByte uint8 = (s).Select(3).(uint8)
  _ = _177_fourthByte
  return ((((((_174_firstByte) == (uint8(240))) && (((uint8(144)) <= (_175_secondByte)) && ((_175_secondByte) <= (uint8(191))))) || ((((uint8(241)) <= (_174_firstByte)) && ((_174_firstByte) <= (uint8(243)))) && (((uint8(128)) <= (_175_secondByte)) && ((_175_secondByte) <= (uint8(191)))))) || (((_174_firstByte) == (uint8(244))) && (((uint8(128)) <= (_175_secondByte)) && ((_175_secondByte) <= (uint8(143)))))) && (((uint8(128)) <= (_176_thirdByte)) && ((_176_thirdByte) <= (uint8(191))))) && (((uint8(128)) <= (_177_fourthByte)) && ((_177_fourthByte) <= (uint8(191))))
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
  var _178_x uint8 = uint8((v) & (uint32(127)))
  _ = _178_x
  var _179_firstByte uint8 = uint8(_178_x)
  _ = _179_firstByte
  return _dafny.SeqOf(_179_firstByte)
}
func (_static *CompanionStruct_Default___) EncodeScalarValueDoubleByte(v uint32) _dafny.Sequence {
  var _180_x uint8 = uint8((v) & (uint32(63)))
  _ = _180_x
  var _181_y uint8 = uint8(((v) & (uint32(1984))) >> (uint8(6)))
  _ = _181_y
  var _182_firstByte uint8 = (uint8(192)) | (uint8(_181_y))
  _ = _182_firstByte
  var _183_secondByte uint8 = (uint8(128)) | (uint8(_180_x))
  _ = _183_secondByte
  return _dafny.SeqOf(_182_firstByte, _183_secondByte)
}
func (_static *CompanionStruct_Default___) EncodeScalarValueTripleByte(v uint32) _dafny.Sequence {
  var _184_x uint8 = uint8((v) & (uint32(63)))
  _ = _184_x
  var _185_y uint8 = uint8(((v) & (uint32(4032))) >> (uint8(6)))
  _ = _185_y
  var _186_z uint8 = uint8(((v) & (uint32(61440))) >> (uint8(12)))
  _ = _186_z
  var _187_firstByte uint8 = (uint8(224)) | (uint8(_186_z))
  _ = _187_firstByte
  var _188_secondByte uint8 = (uint8(128)) | (uint8(_185_y))
  _ = _188_secondByte
  var _189_thirdByte uint8 = (uint8(128)) | (uint8(_184_x))
  _ = _189_thirdByte
  return _dafny.SeqOf(_187_firstByte, _188_secondByte, _189_thirdByte)
}
func (_static *CompanionStruct_Default___) EncodeScalarValueQuadrupleByte(v uint32) _dafny.Sequence {
  var _190_x uint8 = uint8((v) & (uint32(63)))
  _ = _190_x
  var _191_y uint8 = uint8(((v) & (uint32(4032))) >> (uint8(6)))
  _ = _191_y
  var _192_z uint8 = uint8(((v) & (uint32(61440))) >> (uint8(12)))
  _ = _192_z
  var _193_u2 uint8 = uint8(((v) & (uint32(196608))) >> (uint8(16)))
  _ = _193_u2
  var _194_u1 uint8 = uint8(((v) & (uint32(1835008))) >> (uint8(18)))
  _ = _194_u1
  var _195_firstByte uint8 = (uint8(240)) | (uint8(_194_u1))
  _ = _195_firstByte
  var _196_secondByte uint8 = ((uint8(128)) | ((uint8(_193_u2)) << (uint8(4)))) | (uint8(_192_z))
  _ = _196_secondByte
  var _197_thirdByte uint8 = (uint8(128)) | (uint8(_191_y))
  _ = _197_thirdByte
  var _198_fourthByte uint8 = (uint8(128)) | (uint8(_190_x))
  _ = _198_fourthByte
  return _dafny.SeqOf(_195_firstByte, _196_secondByte, _197_thirdByte, _198_fourthByte)
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
  var _199_firstByte uint8 = (m).Select(0).(uint8)
  _ = _199_firstByte
  var _200_x uint8 = uint8(_199_firstByte)
  _ = _200_x
  return uint32(_200_x)
}
func (_static *CompanionStruct_Default___) DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m _dafny.Sequence) uint32 {
  var _201_firstByte uint8 = (m).Select(0).(uint8)
  _ = _201_firstByte
  var _202_secondByte uint8 = (m).Select(1).(uint8)
  _ = _202_secondByte
  var _203_y uint32 = uint32((_201_firstByte) & (uint8(31)))
  _ = _203_y
  var _204_x uint32 = uint32((_202_secondByte) & (uint8(63)))
  _ = _204_x
  return ((((_203_y) << (uint8(6))) & 0xFFFFFF)) | ((_204_x))
}
func (_static *CompanionStruct_Default___) DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m _dafny.Sequence) uint32 {
  var _205_firstByte uint8 = (m).Select(0).(uint8)
  _ = _205_firstByte
  var _206_secondByte uint8 = (m).Select(1).(uint8)
  _ = _206_secondByte
  var _207_thirdByte uint8 = (m).Select(2).(uint8)
  _ = _207_thirdByte
  var _208_z uint32 = uint32((_205_firstByte) & (uint8(15)))
  _ = _208_z
  var _209_y uint32 = uint32((_206_secondByte) & (uint8(63)))
  _ = _209_y
  var _210_x uint32 = uint32((_207_thirdByte) & (uint8(63)))
  _ = _210_x
  return (((((_208_z) << (uint8(12))) & 0xFFFFFF)) | ((((_209_y) << (uint8(6))) & 0xFFFFFF))) | ((_210_x))
}
func (_static *CompanionStruct_Default___) DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(m _dafny.Sequence) uint32 {
  var _211_firstByte uint8 = (m).Select(0).(uint8)
  _ = _211_firstByte
  var _212_secondByte uint8 = (m).Select(1).(uint8)
  _ = _212_secondByte
  var _213_thirdByte uint8 = (m).Select(2).(uint8)
  _ = _213_thirdByte
  var _214_fourthByte uint8 = (m).Select(3).(uint8)
  _ = _214_fourthByte
  var _215_u1 uint32 = uint32((_211_firstByte) & (uint8(7)))
  _ = _215_u1
  var _216_u2 uint32 = uint32(((_212_secondByte) & (uint8(48))) >> (uint8(4)))
  _ = _216_u2
  var _217_z uint32 = uint32((_212_secondByte) & (uint8(15)))
  _ = _217_z
  var _218_y uint32 = uint32((_213_thirdByte) & (uint8(63)))
  _ = _218_y
  var _219_x uint32 = uint32((_214_fourthByte) & (uint8(63)))
  _ = _219_x
  return (((((((_215_u1) << (uint8(18))) & 0xFFFFFF)) | ((((_216_u2) << (uint8(16))) & 0xFFFFFF))) | ((((_217_z) << (uint8(12))) & 0xFFFFFF))) | ((((_218_y) << (uint8(6))) & 0xFFFFFF))) | ((_219_x))
}
func (_static *CompanionStruct_Default___) PartitionCodeUnitSequenceChecked(s _dafny.Sequence) Std_Wrappers.Option {
  var maybeParts Std_Wrappers.Option = Std_Wrappers.Companion_Option_.Default()
  _ = maybeParts
  if (_dafny.Companion_Sequence_.Equal(s, _dafny.SeqOf())) {
    maybeParts = Std_Wrappers.Companion_Option_.Create_Some_(_dafny.SeqOf())
    return maybeParts
  }
  var _220_result _dafny.Sequence
  _ = _220_result
  _220_result = _dafny.SeqOf()
  var _221_rest _dafny.Sequence
  _ = _221_rest
  _221_rest = s
  for (_dafny.IntOfUint32((_221_rest).Cardinality())).Sign() == 1 {
    var _222_prefix _dafny.Sequence
    _ = _222_prefix
    var _223_valueOrError0 Std_Wrappers.Option = Std_Wrappers.Companion_Option_.Default()
    _ = _223_valueOrError0
    _223_valueOrError0 = Companion_Default___.SplitPrefixMinimalWellFormedCodeUnitSubsequence(_221_rest)
    if ((_223_valueOrError0).IsFailure()) {
      maybeParts = (_223_valueOrError0).PropagateFailure()
      return maybeParts
    }
    _222_prefix = (_223_valueOrError0).Extract().(_dafny.Sequence)
    _220_result = _dafny.Companion_Sequence_.Concatenate(_220_result, _dafny.SeqOf(_222_prefix))
    _221_rest = (_221_rest).Drop((_dafny.IntOfUint32((_222_prefix).Cardinality())).Uint32())
  }
  maybeParts = Std_Wrappers.Companion_Option_.Create_Some_(_220_result)
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
  for _224_i := _dafny.IntOfUint32((vs).Cardinality()); _lo0.Cmp(_224_i) < 0;  {
    _224_i = _224_i.Minus(_dafny.One)
    var _225_next _dafny.Sequence
    _ = _225_next
    _225_next = Companion_Default___.EncodeScalarValue((vs).Select((_224_i).Uint32()).(uint32))
    s = _dafny.Companion_Sequence_.Concatenate(_225_next, s)
  }
  return s
}
func (_static *CompanionStruct_Default___) DecodeCodeUnitSequence(s _dafny.Sequence) _dafny.Sequence {
  var _226_parts _dafny.Sequence = Companion_Default___.PartitionCodeUnitSequence(s)
  _ = _226_parts
  var _227_vs _dafny.Sequence = Std_Collections_Seq.Companion_Default___.Map(func (coer6 func (_dafny.Sequence) uint32) func (interface{}) interface{} {
    return func (arg8 interface{}) interface{} {
      return coer6(arg8.(_dafny.Sequence))
    }
  }(Companion_Default___.DecodeMinimalWellFormedCodeUnitSubsequence), _226_parts)
  _ = _227_vs
  return _227_vs
}
func (_static *CompanionStruct_Default___) DecodeCodeUnitSequenceChecked(s _dafny.Sequence) Std_Wrappers.Option {
  var maybeVs Std_Wrappers.Option = Std_Wrappers.Companion_Option_.Default()
  _ = maybeVs
  var _228_maybeParts Std_Wrappers.Option
  _ = _228_maybeParts
  _228_maybeParts = Companion_Default___.PartitionCodeUnitSequenceChecked(s)
  if ((_228_maybeParts).Is_None()) {
    maybeVs = Std_Wrappers.Companion_Option_.Create_None_()
    return maybeVs
  }
  var _229_parts _dafny.Sequence
  _ = _229_parts
  _229_parts = (_228_maybeParts).Dtor_value().(_dafny.Sequence)
  var _230_vs _dafny.Sequence
  _ = _230_vs
  _230_vs = Std_Collections_Seq.Companion_Default___.Map(func (coer7 func (_dafny.Sequence) uint32) func (interface{}) interface{} {
    return func (arg9 interface{}) interface{} {
      return coer7(arg9.(_dafny.Sequence))
    }
  }(Companion_Default___.DecodeMinimalWellFormedCodeUnitSubsequence), _229_parts)
  maybeVs = Std_Wrappers.Companion_Option_.Create_Some_(_230_vs)
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
