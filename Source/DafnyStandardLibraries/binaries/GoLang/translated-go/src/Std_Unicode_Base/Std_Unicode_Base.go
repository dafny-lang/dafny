// Package Std_Unicode_Base
// Dafny module Std_Unicode_Base compiled into Go

package Std_Unicode_Base

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
  return "Std_Unicode_Base.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) IsInAssignedPlane(i uint32) bool {
  var _163_plane uint8 = uint8((i) >> (uint8(16)))
  _ = _163_plane
  return (Companion_Default___.ASSIGNED__PLANES()).Contains(_163_plane)
}
func (_static *CompanionStruct_Default___) HIGH__SURROGATE__MIN() uint32 {
  return uint32(55296)
}
func (_static *CompanionStruct_Default___) HIGH__SURROGATE__MAX() uint32 {
  return uint32(56319)
}
func (_static *CompanionStruct_Default___) LOW__SURROGATE__MIN() uint32 {
  return uint32(56320)
}
func (_static *CompanionStruct_Default___) LOW__SURROGATE__MAX() uint32 {
  return uint32(57343)
}
func (_static *CompanionStruct_Default___) ASSIGNED__PLANES() _dafny.Set {
  return _dafny.SetOf(uint8(0), uint8(1), uint8(2), uint8(3), uint8(14), uint8(15), uint8(16))
}
// End of class Default__

// Definition of class CodePoint
type CodePoint struct {
}

func New_CodePoint_() *CodePoint {
  _this := CodePoint{}

  return &_this
}

type CompanionStruct_CodePoint_ struct {
}
var Companion_CodePoint_ = CompanionStruct_CodePoint_ {
}

func (*CodePoint) String() string {
  return "Std_Unicode_Base.CodePoint"
}
// End of class CodePoint

func Type_CodePoint_() _dafny.TypeDescriptor {
  return type_CodePoint_{}
}

type type_CodePoint_ struct {
}

func (_this type_CodePoint_) Default() interface{} {
  return 0
}

func (_this type_CodePoint_) String() string {
  return "Std_Unicode_Base.CodePoint"
}

// Definition of class HighSurrogateCodePoint
type HighSurrogateCodePoint struct {
}

func New_HighSurrogateCodePoint_() *HighSurrogateCodePoint {
  _this := HighSurrogateCodePoint{}

  return &_this
}

type CompanionStruct_HighSurrogateCodePoint_ struct {
}
var Companion_HighSurrogateCodePoint_ = CompanionStruct_HighSurrogateCodePoint_ {
}

func (*HighSurrogateCodePoint) String() string {
  return "Std_Unicode_Base.HighSurrogateCodePoint"
}
func (_this *CompanionStruct_HighSurrogateCodePoint_) Witness() uint32 {
  return Companion_Default___.HIGH__SURROGATE__MIN()
}
// End of class HighSurrogateCodePoint

func Type_HighSurrogateCodePoint_() _dafny.TypeDescriptor {
  return type_HighSurrogateCodePoint_{}
}

type type_HighSurrogateCodePoint_ struct {
}

func (_this type_HighSurrogateCodePoint_) Default() interface{} {
  return Companion_HighSurrogateCodePoint_.Witness()
}

func (_this type_HighSurrogateCodePoint_) String() string {
  return "Std_Unicode_Base.HighSurrogateCodePoint"
}

// Definition of class LowSurrogateCodePoint
type LowSurrogateCodePoint struct {
}

func New_LowSurrogateCodePoint_() *LowSurrogateCodePoint {
  _this := LowSurrogateCodePoint{}

  return &_this
}

type CompanionStruct_LowSurrogateCodePoint_ struct {
}
var Companion_LowSurrogateCodePoint_ = CompanionStruct_LowSurrogateCodePoint_ {
}

func (*LowSurrogateCodePoint) String() string {
  return "Std_Unicode_Base.LowSurrogateCodePoint"
}
func (_this *CompanionStruct_LowSurrogateCodePoint_) Witness() uint32 {
  return Companion_Default___.LOW__SURROGATE__MIN()
}
// End of class LowSurrogateCodePoint

func Type_LowSurrogateCodePoint_() _dafny.TypeDescriptor {
  return type_LowSurrogateCodePoint_{}
}

type type_LowSurrogateCodePoint_ struct {
}

func (_this type_LowSurrogateCodePoint_) Default() interface{} {
  return Companion_LowSurrogateCodePoint_.Witness()
}

func (_this type_LowSurrogateCodePoint_) String() string {
  return "Std_Unicode_Base.LowSurrogateCodePoint"
}

// Definition of class ScalarValue
type ScalarValue struct {
}

func New_ScalarValue_() *ScalarValue {
  _this := ScalarValue{}

  return &_this
}

type CompanionStruct_ScalarValue_ struct {
}
var Companion_ScalarValue_ = CompanionStruct_ScalarValue_ {
}

func (*ScalarValue) String() string {
  return "Std_Unicode_Base.ScalarValue"
}
// End of class ScalarValue

func Type_ScalarValue_() _dafny.TypeDescriptor {
  return type_ScalarValue_{}
}

type type_ScalarValue_ struct {
}

func (_this type_ScalarValue_) Default() interface{} {
  return 0
}

func (_this type_ScalarValue_) String() string {
  return "Std_Unicode_Base.ScalarValue"
}

// Definition of class AssignedCodePoint
type AssignedCodePoint struct {
}

func New_AssignedCodePoint_() *AssignedCodePoint {
  _this := AssignedCodePoint{}

  return &_this
}

type CompanionStruct_AssignedCodePoint_ struct {
}
var Companion_AssignedCodePoint_ = CompanionStruct_AssignedCodePoint_ {
}

func (*AssignedCodePoint) String() string {
  return "Std_Unicode_Base.AssignedCodePoint"
}
// End of class AssignedCodePoint

func Type_AssignedCodePoint_() _dafny.TypeDescriptor {
  return type_AssignedCodePoint_{}
}

type type_AssignedCodePoint_ struct {
}

func (_this type_AssignedCodePoint_) Default() interface{} {
  return 0
}

func (_this type_AssignedCodePoint_) String() string {
  return "Std_Unicode_Base.AssignedCodePoint"
}
