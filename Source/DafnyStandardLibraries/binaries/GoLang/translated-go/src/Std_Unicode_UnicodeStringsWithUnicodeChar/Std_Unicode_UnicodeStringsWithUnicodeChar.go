// Package Std_Unicode_UnicodeStringsWithUnicodeChar
// Dafny module Std_Unicode_UnicodeStringsWithUnicodeChar compiled into Go

package Std_Unicode_UnicodeStringsWithUnicodeChar

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
  return "Std_Unicode_UnicodeStringsWithUnicodeChar.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) CharAsUnicodeScalarValue(c _dafny.CodePoint) uint32 {
  return uint32(c)
}
func (_static *CompanionStruct_Default___) CharFromUnicodeScalarValue(sv uint32) _dafny.CodePoint {
  return _dafny.CodePoint((_dafny.IntOfUint32(sv)).Int32())
}
func (_static *CompanionStruct_Default___) ToUTF8Checked(s _dafny.Sequence) Std_Wrappers.Option {
  var _262_asCodeUnits _dafny.Sequence = Std_Collections_Seq.Companion_Default___.Map(func (coer10 func (_dafny.CodePoint) uint32) func (interface{}) interface{} {
    return func (arg12 interface{}) interface{} {
      return coer10(arg12.(_dafny.CodePoint))
    }
  }(Companion_Default___.CharAsUnicodeScalarValue), s)
  _ = _262_asCodeUnits
  var _263_asUtf8CodeUnits _dafny.Sequence = Std_Unicode_Utf8EncodingForm.Companion_Default___.EncodeScalarSequence(_262_asCodeUnits)
  _ = _263_asUtf8CodeUnits
  var _264_asBytes _dafny.Sequence = Std_Collections_Seq.Companion_Default___.Map(func (coer11 func (uint8) uint8) func (interface{}) interface{} {
    return func (arg13 interface{}) interface{} {
      return coer11(arg13.(uint8))
    }
  }(func (_265_cu uint8) uint8 {
    return uint8(_265_cu)
  }), _263_asUtf8CodeUnits)
  _ = _264_asBytes
  return Std_Wrappers.Companion_Option_.Create_Some_(_264_asBytes)
}
func (_static *CompanionStruct_Default___) FromUTF8Checked(bs _dafny.Sequence) Std_Wrappers.Option {
  var _266_asCodeUnits _dafny.Sequence = Std_Collections_Seq.Companion_Default___.Map(func (coer12 func (uint8) uint8) func (interface{}) interface{} {
    return func (arg14 interface{}) interface{} {
      return coer12(arg14.(uint8))
    }
  }(func (_267_c uint8) uint8 {
    return uint8(_267_c)
  }), bs)
  _ = _266_asCodeUnits
  var _268_valueOrError0 Std_Wrappers.Option = Std_Unicode_Utf8EncodingForm.Companion_Default___.DecodeCodeUnitSequenceChecked(_266_asCodeUnits)
  _ = _268_valueOrError0
  if ((_268_valueOrError0).IsFailure()) {
    return (_268_valueOrError0).PropagateFailure()
  } else {
    var _269_utf32 _dafny.Sequence = (_268_valueOrError0).Extract().(_dafny.Sequence)
    _ = _269_utf32
    var _270_asChars _dafny.Sequence = Std_Collections_Seq.Companion_Default___.Map(func (coer13 func (uint32) _dafny.CodePoint) func (interface{}) interface{} {
      return func (arg15 interface{}) interface{} {
        return coer13(arg15.(uint32))
      }
    }(Companion_Default___.CharFromUnicodeScalarValue), _269_utf32)
    _ = _270_asChars
    return Std_Wrappers.Companion_Option_.Create_Some_(_270_asChars)
  }
}
func (_static *CompanionStruct_Default___) ToUTF16Checked(s _dafny.Sequence) Std_Wrappers.Option {
  var _271_asCodeUnits _dafny.Sequence = Std_Collections_Seq.Companion_Default___.Map(func (coer14 func (_dafny.CodePoint) uint32) func (interface{}) interface{} {
    return func (arg16 interface{}) interface{} {
      return coer14(arg16.(_dafny.CodePoint))
    }
  }(Companion_Default___.CharAsUnicodeScalarValue), s)
  _ = _271_asCodeUnits
  var _272_asUtf16CodeUnits _dafny.Sequence = Std_Unicode_Utf16EncodingForm.Companion_Default___.EncodeScalarSequence(_271_asCodeUnits)
  _ = _272_asUtf16CodeUnits
  var _273_asBytes _dafny.Sequence = Std_Collections_Seq.Companion_Default___.Map(func (coer15 func (uint16) uint16) func (interface{}) interface{} {
    return func (arg17 interface{}) interface{} {
      return coer15(arg17.(uint16))
    }
  }(func (_274_cu uint16) uint16 {
    return uint16(_274_cu)
  }), _272_asUtf16CodeUnits)
  _ = _273_asBytes
  return Std_Wrappers.Companion_Option_.Create_Some_(_273_asBytes)
}
func (_static *CompanionStruct_Default___) FromUTF16Checked(bs _dafny.Sequence) Std_Wrappers.Option {
  var _275_asCodeUnits _dafny.Sequence = Std_Collections_Seq.Companion_Default___.Map(func (coer16 func (uint16) uint16) func (interface{}) interface{} {
    return func (arg18 interface{}) interface{} {
      return coer16(arg18.(uint16))
    }
  }(func (_276_c uint16) uint16 {
    return uint16(_276_c)
  }), bs)
  _ = _275_asCodeUnits
  var _277_valueOrError0 Std_Wrappers.Option = Std_Unicode_Utf16EncodingForm.Companion_Default___.DecodeCodeUnitSequenceChecked(_275_asCodeUnits)
  _ = _277_valueOrError0
  if ((_277_valueOrError0).IsFailure()) {
    return (_277_valueOrError0).PropagateFailure()
  } else {
    var _278_utf32 _dafny.Sequence = (_277_valueOrError0).Extract().(_dafny.Sequence)
    _ = _278_utf32
    var _279_asChars _dafny.Sequence = Std_Collections_Seq.Companion_Default___.Map(func (coer17 func (uint32) _dafny.CodePoint) func (interface{}) interface{} {
      return func (arg19 interface{}) interface{} {
        return coer17(arg19.(uint32))
      }
    }(Companion_Default___.CharFromUnicodeScalarValue), _278_utf32)
    _ = _279_asChars
    return Std_Wrappers.Companion_Option_.Create_Some_(_279_asChars)
  }
}
func (_static *CompanionStruct_Default___) ASCIIToUTF8(s _dafny.Sequence) _dafny.Sequence {
  return Std_Collections_Seq.Companion_Default___.Map(func (coer18 func (_dafny.CodePoint) uint8) func (interface{}) interface{} {
    return func (arg20 interface{}) interface{} {
      return coer18(arg20.(_dafny.CodePoint))
    }
  }(func (_280_c _dafny.CodePoint) uint8 {
    return uint8(_280_c)
  }), s)
}
func (_static *CompanionStruct_Default___) ASCIIToUTF16(s _dafny.Sequence) _dafny.Sequence {
  return Std_Collections_Seq.Companion_Default___.Map(func (coer19 func (_dafny.CodePoint) uint16) func (interface{}) interface{} {
    return func (arg21 interface{}) interface{} {
      return coer19(arg21.(_dafny.CodePoint))
    }
  }(func (_281_c _dafny.CodePoint) uint16 {
    return uint16(_281_c)
  }), s)
}
// End of class Default__
