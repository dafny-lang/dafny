// Package Std_Base64
// Dafny module Std_Base64 compiled into Go

package Std_Base64

import (
  _dafny "dafny"
  os "os"
  _System "System_"
  Std_Wrappers "Std_Wrappers"
  Std_Concurrent "Std_Concurrent"
  Std_FileIOInternalExterns "Std_FileIOInternalExterns"
  Std_BoundedInts "Std_BoundedInts"
)
var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Std_Wrappers.Dummy__
var _ Std_Concurrent.Dummy__
var _ = Std_FileIOInternalExterns.INTERNAL__ReadBytesFromFile
var _ Std_BoundedInts.Dummy__

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
  return "Std_Base64.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) IsBase64Char(c _dafny.CodePoint) bool {
  return (((((c) == (_dafny.CodePoint('+'))) || ((c) == (_dafny.CodePoint('/')))) || (((_dafny.CodePoint('0')) <= (c)) && ((c) <= (_dafny.CodePoint('9'))))) || (((_dafny.CodePoint('A')) <= (c)) && ((c) <= (_dafny.CodePoint('Z'))))) || (((_dafny.CodePoint('a')) <= (c)) && ((c) <= (_dafny.CodePoint('z'))))
}
func (_static *CompanionStruct_Default___) IsUnpaddedBase64String(s _dafny.Sequence) bool {
  return (((_dafny.IntOfUint32((s).Cardinality())).Modulo(_dafny.IntOfInt64(4))).Sign() == 0) && (_dafny.Quantifier((s).UniqueElements(), true, func (_forall_var_0 _dafny.CodePoint) bool {
    var _28_k _dafny.CodePoint
    _28_k = interface{}(_forall_var_0).(_dafny.CodePoint)
    return !(_dafny.Companion_Sequence_.Contains(s, _28_k)) || (Companion_Default___.IsBase64Char(_28_k))
  }))
}
func (_static *CompanionStruct_Default___) IndexToChar(i uint8) _dafny.CodePoint {
  if ((i) == (uint8(63))) {
    return _dafny.CodePoint('/')
  } else if ((i) == (uint8(62))) {
    return _dafny.CodePoint('+')
  } else if (((uint8(52)) <= (i)) && ((i) <= (uint8(61)))) {
    return _dafny.CodePoint(((((i) - (func () uint8 { return  (uint8(4)) })()) & 0x3F)))
  } else if (((uint8(26)) <= (i)) && ((i) <= (uint8(51)))) {
    return (_dafny.CodePoint((i))) + (_dafny.CodePoint((_dafny.IntOfInt64(71)).Int32()))
  } else {
    return (_dafny.CodePoint((i))) + (_dafny.CodePoint((_dafny.IntOfInt64(65)).Int32()))
  }
}
func (_static *CompanionStruct_Default___) CharToIndex(c _dafny.CodePoint) uint8 {
  if ((c) == (_dafny.CodePoint('/'))) {
    return uint8(63)
  } else if ((c) == (_dafny.CodePoint('+'))) {
    return uint8(62)
  } else if (((_dafny.CodePoint('0')) <= (c)) && ((c) <= (_dafny.CodePoint('9')))) {
    return uint8((c) + (_dafny.CodePoint((_dafny.IntOfInt64(4)).Int32())))
  } else if (((_dafny.CodePoint('a')) <= (c)) && ((c) <= (_dafny.CodePoint('z')))) {
    return uint8((c) - (_dafny.CodePoint((_dafny.IntOfInt64(71)).Int32())))
  } else {
    return uint8((c) - (_dafny.CodePoint((_dafny.IntOfInt64(65)).Int32())))
  }
}
func (_static *CompanionStruct_Default___) BV24ToSeq(x uint32) _dafny.Sequence {
  var _29_b0 uint8 = uint8(((x) >> (uint8(16))) & (uint32(255)))
  _ = _29_b0
  var _30_b1 uint8 = uint8(((x) >> (uint8(8))) & (uint32(255)))
  _ = _30_b1
  var _31_b2 uint8 = uint8((x) & (uint32(255)))
  _ = _31_b2
  return _dafny.SeqOf(_29_b0, _30_b1, _31_b2)
}
func (_static *CompanionStruct_Default___) SeqToBV24(x _dafny.Sequence) uint32 {
  return (((((uint32((x).Select(0).(uint8))) << (uint8(16))) & 0xFFFFFF)) | ((((uint32((x).Select(1).(uint8))) << (uint8(8))) & 0xFFFFFF))) | (uint32((x).Select(2).(uint8)))
}
func (_static *CompanionStruct_Default___) BV24ToIndexSeq(x uint32) _dafny.Sequence {
  var _32_b0 uint8 = uint8(((x) >> (uint8(18))) & (uint32(63)))
  _ = _32_b0
  var _33_b1 uint8 = uint8(((x) >> (uint8(12))) & (uint32(63)))
  _ = _33_b1
  var _34_b2 uint8 = uint8(((x) >> (uint8(6))) & (uint32(63)))
  _ = _34_b2
  var _35_b3 uint8 = uint8((x) & (uint32(63)))
  _ = _35_b3
  return _dafny.SeqOf(_32_b0, _33_b1, _34_b2, _35_b3)
}
func (_static *CompanionStruct_Default___) IndexSeqToBV24(x _dafny.Sequence) uint32 {
  return ((((((uint32((x).Select(0).(uint8))) << (uint8(18))) & 0xFFFFFF)) | ((((uint32((x).Select(1).(uint8))) << (uint8(12))) & 0xFFFFFF))) | ((((uint32((x).Select(2).(uint8))) << (uint8(6))) & 0xFFFFFF))) | (uint32((x).Select(3).(uint8)))
}
func (_static *CompanionStruct_Default___) DecodeBlock(s _dafny.Sequence) _dafny.Sequence {
  return Companion_Default___.BV24ToSeq(Companion_Default___.IndexSeqToBV24(s))
}
func (_static *CompanionStruct_Default___) EncodeBlock(s _dafny.Sequence) _dafny.Sequence {
  return Companion_Default___.BV24ToIndexSeq(Companion_Default___.SeqToBV24(s))
}
func (_static *CompanionStruct_Default___) DecodeRecursively(s _dafny.Sequence) _dafny.Sequence {
  var b _dafny.Sequence = _dafny.EmptySeq
  _ = b
  var _36_resultLength _dafny.Int
  _ = _36_resultLength
  _36_resultLength = ((_dafny.IntOfUint32((s).Cardinality())).DivBy(_dafny.IntOfInt64(4))).Times(_dafny.IntOfInt64(3))
  var _37_result _dafny.Array
  _ = _37_result
  var _len0_0 _dafny.Int = _36_resultLength
  _ = _len0_0
  var _nw0 _dafny.Array
  _ = _nw0
  if (_len0_0.Cmp(_dafny.Zero) == 0) {
    _nw0 = _dafny.NewArray(_len0_0)
  } else {
    var _init0 func (_dafny.Int) uint8 = func (_38_i _dafny.Int) uint8 {
      return uint8(0)
    }
    _ = _init0
    var _element0_0 = _init0(_dafny.Zero)
    _ = _element0_0
    _nw0 = _dafny.NewArrayFromExample(_element0_0, nil, _len0_0)
    (_nw0).ArraySet1Byte(_element0_0, 0)
    var _nativeLen0_0 = (_len0_0).Int()
    _ = _nativeLen0_0
    for _i0_0 := 1; _i0_0 < _nativeLen0_0; _i0_0++ {
      (_nw0).ArraySet1Byte(_init0(_dafny.IntOf(_i0_0)), _i0_0)
    }
  }
  _37_result = _nw0
  var _39_i _dafny.Int
  _ = _39_i
  _39_i = _dafny.IntOfUint32((s).Cardinality())
  var _40_j _dafny.Int
  _ = _40_j
  _40_j = _36_resultLength
  for (_39_i).Sign() == 1 {
    _39_i = (_39_i).Minus(_dafny.IntOfInt64(4))
    _40_j = (_40_j).Minus(_dafny.IntOfInt64(3))
    var _41_block _dafny.Sequence
    _ = _41_block
    _41_block = Companion_Default___.DecodeBlock((s).Subsequence((_39_i).Uint32(), ((_39_i).Plus(_dafny.IntOfInt64(4))).Uint32()))
    ((_37_result)).ArraySet1Byte((_41_block).Select(0).(uint8), ((_40_j)).Int())
    var _index0 _dafny.Int = (_40_j).Plus(_dafny.One)
    _ = _index0
    ((_37_result)).ArraySet1Byte((_41_block).Select(1).(uint8), (_index0).Int())
    var _index1 _dafny.Int = (_40_j).Plus(_dafny.IntOfInt64(2))
    _ = _index1
    ((_37_result)).ArraySet1Byte((_41_block).Select(2).(uint8), (_index1).Int())
  }
  b = _dafny.ArrayRangeToSeq(_37_result, _dafny.NilInt, _dafny.NilInt)
  return b
}
func (_static *CompanionStruct_Default___) EncodeRecursively(b _dafny.Sequence) _dafny.Sequence {
  var s _dafny.Sequence = _dafny.EmptySeq
  _ = s
  var _42_resultLength _dafny.Int
  _ = _42_resultLength
  _42_resultLength = ((_dafny.IntOfUint32((b).Cardinality())).DivBy(_dafny.IntOfInt64(3))).Times(_dafny.IntOfInt64(4))
  var _43_result _dafny.Array
  _ = _43_result
  var _len0_1 _dafny.Int = _42_resultLength
  _ = _len0_1
  var _nw1 _dafny.Array
  _ = _nw1
  if (_len0_1.Cmp(_dafny.Zero) == 0) {
    _nw1 = _dafny.NewArray(_len0_1)
  } else {
    var _init1 func (_dafny.Int) uint8 = func (_44_i _dafny.Int) uint8 {
      return uint8(0)
    }
    _ = _init1
    var _element0_1 = _init1(_dafny.Zero)
    _ = _element0_1
    _nw1 = _dafny.NewArrayFromExample(_element0_1, nil, _len0_1)
    (_nw1).ArraySet1Byte(_element0_1, 0)
    var _nativeLen0_1 = (_len0_1).Int()
    _ = _nativeLen0_1
    for _i0_1 := 1; _i0_1 < _nativeLen0_1; _i0_1++ {
      (_nw1).ArraySet1Byte(_init1(_dafny.IntOf(_i0_1)), _i0_1)
    }
  }
  _43_result = _nw1
  var _45_i _dafny.Int
  _ = _45_i
  _45_i = _dafny.IntOfUint32((b).Cardinality())
  var _46_j _dafny.Int
  _ = _46_j
  _46_j = _42_resultLength
  for (_45_i).Sign() == 1 {
    _45_i = (_45_i).Minus(_dafny.IntOfInt64(3))
    _46_j = (_46_j).Minus(_dafny.IntOfInt64(4))
    var _47_block _dafny.Sequence
    _ = _47_block
    _47_block = Companion_Default___.EncodeBlock((b).Subsequence((_45_i).Uint32(), ((_45_i).Plus(_dafny.IntOfInt64(3))).Uint32()))
    ((_43_result)).ArraySet1Byte((_47_block).Select(0).(uint8), ((_46_j)).Int())
    var _index2 _dafny.Int = (_46_j).Plus(_dafny.One)
    _ = _index2
    ((_43_result)).ArraySet1Byte((_47_block).Select(1).(uint8), (_index2).Int())
    var _index3 _dafny.Int = (_46_j).Plus(_dafny.IntOfInt64(2))
    _ = _index3
    ((_43_result)).ArraySet1Byte((_47_block).Select(2).(uint8), (_index3).Int())
    var _index4 _dafny.Int = (_46_j).Plus(_dafny.IntOfInt64(3))
    _ = _index4
    ((_43_result)).ArraySet1Byte((_47_block).Select(3).(uint8), (_index4).Int())
  }
  s = _dafny.ArrayRangeToSeq(_43_result, _dafny.NilInt, _dafny.NilInt)
  return s
}
func (_static *CompanionStruct_Default___) FromCharsToIndices(s _dafny.Sequence) _dafny.Sequence {
  return _dafny.SeqCreate((_dafny.IntOfUint32((s).Cardinality())).Uint32(), func (coer0 func (_dafny.Int) uint8) func (_dafny.Int) interface{} {
    return func (arg0 _dafny.Int) interface{} {
      return coer0(arg0)
    }
  }((func (_48_s _dafny.Sequence) func (_dafny.Int) uint8 {
    return func (_49_i _dafny.Int) uint8 {
      return Companion_Default___.CharToIndex((_48_s).Select((_49_i).Uint32()).(_dafny.CodePoint))
    }
  })(s)))
}
func (_static *CompanionStruct_Default___) FromIndicesToChars(b _dafny.Sequence) _dafny.Sequence {
  return _dafny.SeqCreate((_dafny.IntOfUint32((b).Cardinality())).Uint32(), func (coer1 func (_dafny.Int) _dafny.CodePoint) func (_dafny.Int) interface{} {
    return func (arg1 _dafny.Int) interface{} {
      return coer1(arg1)
    }
  }((func (_50_b _dafny.Sequence) func (_dafny.Int) _dafny.CodePoint {
    return func (_51_i _dafny.Int) _dafny.CodePoint {
      return Companion_Default___.IndexToChar((_50_b).Select((_51_i).Uint32()).(uint8))
    }
  })(b)))
}
func (_static *CompanionStruct_Default___) DecodeUnpadded(s _dafny.Sequence) _dafny.Sequence {
  return Companion_Default___.DecodeRecursively(Companion_Default___.FromCharsToIndices(s))
}
func (_static *CompanionStruct_Default___) EncodeUnpadded(b _dafny.Sequence) _dafny.Sequence {
  return Companion_Default___.FromIndicesToChars(Companion_Default___.EncodeRecursively(b))
}
func (_static *CompanionStruct_Default___) Is1Padding(s _dafny.Sequence) bool {
  return ((((((_dafny.IntOfUint32((s).Cardinality())).Cmp(_dafny.IntOfInt64(4)) == 0) && (Companion_Default___.IsBase64Char((s).Select(0).(_dafny.CodePoint)))) && (Companion_Default___.IsBase64Char((s).Select(1).(_dafny.CodePoint)))) && (Companion_Default___.IsBase64Char((s).Select(2).(_dafny.CodePoint)))) && (((Companion_Default___.CharToIndex((s).Select(2).(_dafny.CodePoint))) & (uint8(3))) == (uint8(0)))) && (((s).Select(3).(_dafny.CodePoint)) == (_dafny.CodePoint('=')))
}
func (_static *CompanionStruct_Default___) Decode1Padding(s _dafny.Sequence) _dafny.Sequence {
  var _52_d _dafny.Sequence = Companion_Default___.DecodeBlock(_dafny.SeqOf(Companion_Default___.CharToIndex((s).Select(0).(_dafny.CodePoint)), Companion_Default___.CharToIndex((s).Select(1).(_dafny.CodePoint)), Companion_Default___.CharToIndex((s).Select(2).(_dafny.CodePoint)), uint8(0)))
  _ = _52_d
  return _dafny.SeqOf((_52_d).Select(0).(uint8), (_52_d).Select(1).(uint8))
}
func (_static *CompanionStruct_Default___) Encode1Padding(b _dafny.Sequence) _dafny.Sequence {
  var _53_e _dafny.Sequence = Companion_Default___.EncodeBlock(_dafny.SeqOf((b).Select(0).(uint8), (b).Select(1).(uint8), uint8(0)))
  _ = _53_e
  return _dafny.SeqOf(Companion_Default___.IndexToChar((_53_e).Select(0).(uint8)), Companion_Default___.IndexToChar((_53_e).Select(1).(uint8)), Companion_Default___.IndexToChar((_53_e).Select(2).(uint8)), _dafny.CodePoint('='))
}
func (_static *CompanionStruct_Default___) Is2Padding(s _dafny.Sequence) bool {
  return ((((((_dafny.IntOfUint32((s).Cardinality())).Cmp(_dafny.IntOfInt64(4)) == 0) && (Companion_Default___.IsBase64Char((s).Select(0).(_dafny.CodePoint)))) && (Companion_Default___.IsBase64Char((s).Select(1).(_dafny.CodePoint)))) && (((Companion_Default___.CharToIndex((s).Select(1).(_dafny.CodePoint))) % (uint8(16))) == (uint8(0)))) && (((s).Select(2).(_dafny.CodePoint)) == (_dafny.CodePoint('=')))) && (((s).Select(3).(_dafny.CodePoint)) == (_dafny.CodePoint('=')))
}
func (_static *CompanionStruct_Default___) Decode2Padding(s _dafny.Sequence) _dafny.Sequence {
  var _54_d _dafny.Sequence = Companion_Default___.DecodeBlock(_dafny.SeqOf(Companion_Default___.CharToIndex((s).Select(0).(_dafny.CodePoint)), Companion_Default___.CharToIndex((s).Select(1).(_dafny.CodePoint)), uint8(0), uint8(0)))
  _ = _54_d
  return _dafny.SeqOf((_54_d).Select(0).(uint8))
}
func (_static *CompanionStruct_Default___) Encode2Padding(b _dafny.Sequence) _dafny.Sequence {
  var _55_e _dafny.Sequence = Companion_Default___.EncodeBlock(_dafny.SeqOf((b).Select(0).(uint8), uint8(0), uint8(0)))
  _ = _55_e
  return _dafny.SeqOf(Companion_Default___.IndexToChar((_55_e).Select(0).(uint8)), Companion_Default___.IndexToChar((_55_e).Select(1).(uint8)), _dafny.CodePoint('='), _dafny.CodePoint('='))
}
func (_static *CompanionStruct_Default___) IsBase64String(s _dafny.Sequence) bool {
  var _56_finalBlockStart _dafny.Int = (_dafny.IntOfUint32((s).Cardinality())).Minus(_dafny.IntOfInt64(4))
  _ = _56_finalBlockStart
  return (((_dafny.IntOfUint32((s).Cardinality())).Modulo(_dafny.IntOfInt64(4))).Sign() == 0) && ((Companion_Default___.IsUnpaddedBase64String(s)) || ((Companion_Default___.IsUnpaddedBase64String((s).Take((_56_finalBlockStart).Uint32()))) && ((Companion_Default___.Is1Padding((s).Drop((_56_finalBlockStart).Uint32()))) || (Companion_Default___.Is2Padding((s).Drop((_56_finalBlockStart).Uint32()))))))
}
func (_static *CompanionStruct_Default___) DecodeValid(s _dafny.Sequence) _dafny.Sequence {
  if (_dafny.Companion_Sequence_.Equal(s, _dafny.SeqOf())) {
    return _dafny.SeqOf()
  } else {
    var _57_finalBlockStart _dafny.Int = (_dafny.IntOfUint32((s).Cardinality())).Minus(_dafny.IntOfInt64(4))
    _ = _57_finalBlockStart
    var _58_prefix _dafny.Sequence = (s).Take((_57_finalBlockStart).Uint32())
    _ = _58_prefix
    var _59_suffix _dafny.Sequence = (s).Drop((_57_finalBlockStart).Uint32())
    _ = _59_suffix
    if (Companion_Default___.Is1Padding(_59_suffix)) {
      return _dafny.Companion_Sequence_.Concatenate(Companion_Default___.DecodeUnpadded(_58_prefix), Companion_Default___.Decode1Padding(_59_suffix))
    } else if (Companion_Default___.Is2Padding(_59_suffix)) {
      return _dafny.Companion_Sequence_.Concatenate(Companion_Default___.DecodeUnpadded(_58_prefix), Companion_Default___.Decode2Padding(_59_suffix))
    } else {
      return Companion_Default___.DecodeUnpadded(s)
    }
  }
}
func (_static *CompanionStruct_Default___) DecodeBV(s _dafny.Sequence) Std_Wrappers.Result {
  if (Companion_Default___.IsBase64String(s)) {
    return Std_Wrappers.Companion_Result_.Create_Success_(Companion_Default___.DecodeValid(s))
  } else {
    return Std_Wrappers.Companion_Result_.Create_Failure_(_dafny.UnicodeSeqOfUtf8Bytes("The encoding is malformed"))
  }
}
func (_static *CompanionStruct_Default___) EncodeBV(b _dafny.Sequence) _dafny.Sequence {
  if (((_dafny.IntOfUint32((b).Cardinality())).Modulo(_dafny.IntOfInt64(3))).Sign() == 0) {
    return Companion_Default___.EncodeUnpadded(b)
  } else if (((_dafny.IntOfUint32((b).Cardinality())).Modulo(_dafny.IntOfInt64(3))).Cmp(_dafny.One) == 0) {
    var _60_s1 _dafny.Sequence = Companion_Default___.EncodeUnpadded((b).Take(((_dafny.IntOfUint32((b).Cardinality())).Minus(_dafny.One)).Uint32()))
    _ = _60_s1
    var _61_s2 _dafny.Sequence = Companion_Default___.Encode2Padding((b).Drop(((_dafny.IntOfUint32((b).Cardinality())).Minus(_dafny.One)).Uint32()))
    _ = _61_s2
    return _dafny.Companion_Sequence_.Concatenate(_60_s1, _61_s2)
  } else {
    var _62_s1 _dafny.Sequence = Companion_Default___.EncodeUnpadded((b).Take(((_dafny.IntOfUint32((b).Cardinality())).Minus(_dafny.IntOfInt64(2))).Uint32()))
    _ = _62_s1
    var _63_s2 _dafny.Sequence = Companion_Default___.Encode1Padding((b).Drop(((_dafny.IntOfUint32((b).Cardinality())).Minus(_dafny.IntOfInt64(2))).Uint32()))
    _ = _63_s2
    return _dafny.Companion_Sequence_.Concatenate(_62_s1, _63_s2)
  }
}
func (_static *CompanionStruct_Default___) UInt8sToBVs(u _dafny.Sequence) _dafny.Sequence {
  return _dafny.SeqCreate((_dafny.IntOfUint32((u).Cardinality())).Uint32(), func (coer2 func (_dafny.Int) uint8) func (_dafny.Int) interface{} {
    return func (arg2 _dafny.Int) interface{} {
      return coer2(arg2)
    }
  }((func (_64_u _dafny.Sequence) func (_dafny.Int) uint8 {
    return func (_65_i _dafny.Int) uint8 {
      return uint8((_64_u).Select((_65_i).Uint32()).(uint8))
    }
  })(u)))
}
func (_static *CompanionStruct_Default___) BVsToUInt8s(b _dafny.Sequence) _dafny.Sequence {
  return _dafny.SeqCreate((_dafny.IntOfUint32((b).Cardinality())).Uint32(), func (coer3 func (_dafny.Int) uint8) func (_dafny.Int) interface{} {
    return func (arg3 _dafny.Int) interface{} {
      return coer3(arg3)
    }
  }((func (_66_b _dafny.Sequence) func (_dafny.Int) uint8 {
    return func (_67_i _dafny.Int) uint8 {
      return uint8((_66_b).Select((_67_i).Uint32()).(uint8))
    }
  })(b)))
}
func (_static *CompanionStruct_Default___) Encode(u _dafny.Sequence) _dafny.Sequence {
  return Companion_Default___.EncodeBV(Companion_Default___.UInt8sToBVs(u))
}
func (_static *CompanionStruct_Default___) Decode(s _dafny.Sequence) Std_Wrappers.Result {
  if (Companion_Default___.IsBase64String(s)) {
    var _68_b _dafny.Sequence = Companion_Default___.DecodeValid(s)
    _ = _68_b
    return Std_Wrappers.Companion_Result_.Create_Success_(Companion_Default___.BVsToUInt8s(_68_b))
  } else {
    return Std_Wrappers.Companion_Result_.Create_Failure_(_dafny.UnicodeSeqOfUtf8Bytes("The encoding is malformed"))
  }
}
// End of class Default__
