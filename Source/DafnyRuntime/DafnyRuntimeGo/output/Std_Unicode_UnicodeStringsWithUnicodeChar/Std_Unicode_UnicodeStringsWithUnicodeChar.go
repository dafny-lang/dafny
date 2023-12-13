// Package Std_Unicode_UnicodeStringsWithUnicodeChar
// Dafny module Std_Unicode_UnicodeStringsWithUnicodeChar compiled into Go

package Std_Unicode_UnicodeStringsWithUnicodeChar

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
)
var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Std_Wrappers.Dummy__
var _ Std_Concurrent.Dummy__
var _ = Std_FileIOInternalExterns.INTERNAL__ReadBytesFromFile
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
  var _270_asCodeUnits _dafny.Sequence = Std_Collections_Seq.Companion_Default___.Map(func (coer12 func (_dafny.CodePoint) uint32) func (interface{}) interface{} {
    return func (arg14 interface{}) interface{} {
      return coer12(arg14.(_dafny.CodePoint))
    }
  }(Companion_Default___.CharAsUnicodeScalarValue), s)
  _ = _270_asCodeUnits
  var _271_asUtf8CodeUnits _dafny.Sequence = Std_Unicode_Utf8EncodingForm.Companion_Default___.EncodeScalarSequence(_270_asCodeUnits)
  _ = _271_asUtf8CodeUnits
  var _272_asBytes _dafny.Sequence = Std_Collections_Seq.Companion_Default___.Map(func (coer13 func (uint8) uint8) func (interface{}) interface{} {
    return func (arg15 interface{}) interface{} {
      return coer13(arg15.(uint8))
    }
  }(func (_273_cu uint8) uint8 {
    return uint8(_273_cu)
  }), _271_asUtf8CodeUnits)
  _ = _272_asBytes
  return Std_Wrappers.Companion_Option_.Create_Some_(_272_asBytes)
}
func (_static *CompanionStruct_Default___) FromUTF8Checked(bs _dafny.Sequence) Std_Wrappers.Option {
  var _274_asCodeUnits _dafny.Sequence = Std_Collections_Seq.Companion_Default___.Map(func (coer14 func (uint8) uint8) func (interface{}) interface{} {
    return func (arg16 interface{}) interface{} {
      return coer14(arg16.(uint8))
    }
  }(func (_275_c uint8) uint8 {
    return uint8(_275_c)
  }), bs)
  _ = _274_asCodeUnits
  var _276_valueOrError0 Std_Wrappers.Option = Std_Unicode_Utf8EncodingForm.Companion_Default___.DecodeCodeUnitSequenceChecked(_274_asCodeUnits)
  _ = _276_valueOrError0
  if ((_276_valueOrError0).IsFailure()) {
    return (_276_valueOrError0).PropagateFailure()
  } else {
    var _277_utf32 _dafny.Sequence = (_276_valueOrError0).Extract().(_dafny.Sequence)
    _ = _277_utf32
    var _278_asChars _dafny.Sequence = Std_Collections_Seq.Companion_Default___.Map(func (coer15 func (uint32) _dafny.CodePoint) func (interface{}) interface{} {
      return func (arg17 interface{}) interface{} {
        return coer15(arg17.(uint32))
      }
    }(Companion_Default___.CharFromUnicodeScalarValue), _277_utf32)
    _ = _278_asChars
    return Std_Wrappers.Companion_Option_.Create_Some_(_278_asChars)
  }
}
func (_static *CompanionStruct_Default___) ToUTF16Checked(s _dafny.Sequence) Std_Wrappers.Option {
  var _279_asCodeUnits _dafny.Sequence = Std_Collections_Seq.Companion_Default___.Map(func (coer16 func (_dafny.CodePoint) uint32) func (interface{}) interface{} {
    return func (arg18 interface{}) interface{} {
      return coer16(arg18.(_dafny.CodePoint))
    }
  }(Companion_Default___.CharAsUnicodeScalarValue), s)
  _ = _279_asCodeUnits
  var _280_asUtf16CodeUnits _dafny.Sequence = Std_Unicode_Utf16EncodingForm.Companion_Default___.EncodeScalarSequence(_279_asCodeUnits)
  _ = _280_asUtf16CodeUnits
  var _281_asBytes _dafny.Sequence = Std_Collections_Seq.Companion_Default___.Map(func (coer17 func (uint16) uint16) func (interface{}) interface{} {
    return func (arg19 interface{}) interface{} {
      return coer17(arg19.(uint16))
    }
  }(func (_282_cu uint16) uint16 {
    return uint16(_282_cu)
  }), _280_asUtf16CodeUnits)
  _ = _281_asBytes
  return Std_Wrappers.Companion_Option_.Create_Some_(_281_asBytes)
}
func (_static *CompanionStruct_Default___) FromUTF16Checked(bs _dafny.Sequence) Std_Wrappers.Option {
  var _283_asCodeUnits _dafny.Sequence = Std_Collections_Seq.Companion_Default___.Map(func (coer18 func (uint16) uint16) func (interface{}) interface{} {
    return func (arg20 interface{}) interface{} {
      return coer18(arg20.(uint16))
    }
  }(func (_284_c uint16) uint16 {
    return uint16(_284_c)
  }), bs)
  _ = _283_asCodeUnits
  var _285_valueOrError0 Std_Wrappers.Option = Std_Unicode_Utf16EncodingForm.Companion_Default___.DecodeCodeUnitSequenceChecked(_283_asCodeUnits)
  _ = _285_valueOrError0
  if ((_285_valueOrError0).IsFailure()) {
    return (_285_valueOrError0).PropagateFailure()
  } else {
    var _286_utf32 _dafny.Sequence = (_285_valueOrError0).Extract().(_dafny.Sequence)
    _ = _286_utf32
    var _287_asChars _dafny.Sequence = Std_Collections_Seq.Companion_Default___.Map(func (coer19 func (uint32) _dafny.CodePoint) func (interface{}) interface{} {
      return func (arg21 interface{}) interface{} {
        return coer19(arg21.(uint32))
      }
    }(Companion_Default___.CharFromUnicodeScalarValue), _286_utf32)
    _ = _287_asChars
    return Std_Wrappers.Companion_Option_.Create_Some_(_287_asChars)
  }
}
func (_static *CompanionStruct_Default___) ASCIIToUTF8(s _dafny.Sequence) _dafny.Sequence {
  return Std_Collections_Seq.Companion_Default___.Map(func (coer20 func (_dafny.CodePoint) uint8) func (interface{}) interface{} {
    return func (arg22 interface{}) interface{} {
      return coer20(arg22.(_dafny.CodePoint))
    }
  }(func (_288_c _dafny.CodePoint) uint8 {
    return uint8(_288_c)
  }), s)
}
func (_static *CompanionStruct_Default___) ASCIIToUTF16(s _dafny.Sequence) _dafny.Sequence {
  return Std_Collections_Seq.Companion_Default___.Map(func (coer21 func (_dafny.CodePoint) uint16) func (interface{}) interface{} {
    return func (arg23 interface{}) interface{} {
      return coer21(arg23.(_dafny.CodePoint))
    }
  }(func (_289_c _dafny.CodePoint) uint16 {
    return uint16(_289_c)
  }), s)
}
// End of class Default__
