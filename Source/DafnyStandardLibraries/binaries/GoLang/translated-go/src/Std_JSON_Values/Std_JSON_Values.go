// Package Std_JSON_Values
// Dafny module Std_JSON_Values compiled into Go

package Std_JSON_Values

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
  return "Std_JSON_Values.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) Int(n _dafny.Int) Decimal {
  return Companion_Decimal_.Create_Decimal_(n, _dafny.Zero)
}
// End of class Default__

// Definition of datatype Decimal
type Decimal struct {
  Data_Decimal_
}

func (_this Decimal) Get_() Data_Decimal_ {
  return _this.Data_Decimal_
}

type Data_Decimal_ interface {
  isDecimal()
}

type CompanionStruct_Decimal_ struct {
}
var Companion_Decimal_ = CompanionStruct_Decimal_ {
}

type Decimal_Decimal struct {
  N _dafny.Int
  E10 _dafny.Int
}

func (Decimal_Decimal) isDecimal() {}

func (CompanionStruct_Decimal_) Create_Decimal_(N _dafny.Int, E10 _dafny.Int) Decimal {
  return Decimal{Decimal_Decimal{N, E10}}
}

func (_this Decimal) Is_Decimal() bool {
  _, ok := _this.Get_().(Decimal_Decimal)
  return ok
}

func (CompanionStruct_Decimal_) Default() Decimal {
  return Companion_Decimal_.Create_Decimal_(_dafny.Zero, _dafny.Zero)
}

func (_this Decimal) Dtor_n() _dafny.Int {
  return _this.Get_().(Decimal_Decimal).N
}

func (_this Decimal) Dtor_e10() _dafny.Int {
  return _this.Get_().(Decimal_Decimal).E10
}

func (_this Decimal) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case Decimal_Decimal: {
      return "Values.Decimal.Decimal" + "(" + _dafny.String(data.N) + ", " + _dafny.String(data.E10) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this Decimal) Equals(other Decimal) bool {
  switch data1 := _this.Get_().(type) {
    case Decimal_Decimal: {
      data2, ok := other.Get_().(Decimal_Decimal)
      return ok && data1.N.Cmp(data2.N) == 0 && data1.E10.Cmp(data2.E10) == 0
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this Decimal) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(Decimal)
  return ok && _this.Equals(typed)
}

func Type_Decimal_() _dafny.TypeDescriptor {
  return type_Decimal_{}
}

type type_Decimal_ struct {
}

func (_this type_Decimal_) Default() interface{} {
  return Companion_Decimal_.Default();
}

func (_this type_Decimal_) String() string {
  return "Std_JSON_Values.Decimal"
}
func (_this Decimal) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Decimal{}

// End of datatype Decimal

// Definition of datatype JSON
type JSON struct {
  Data_JSON_
}

func (_this JSON) Get_() Data_JSON_ {
  return _this.Data_JSON_
}

type Data_JSON_ interface {
  isJSON()
}

type CompanionStruct_JSON_ struct {
}
var Companion_JSON_ = CompanionStruct_JSON_ {
}

type JSON_Null struct {
}

func (JSON_Null) isJSON() {}

func (CompanionStruct_JSON_) Create_Null_() JSON {
  return JSON{JSON_Null{}}
}

func (_this JSON) Is_Null() bool {
  _, ok := _this.Get_().(JSON_Null)
  return ok
}

type JSON_Bool struct {
  B bool
}

func (JSON_Bool) isJSON() {}

func (CompanionStruct_JSON_) Create_Bool_(B bool) JSON {
  return JSON{JSON_Bool{B}}
}

func (_this JSON) Is_Bool() bool {
  _, ok := _this.Get_().(JSON_Bool)
  return ok
}

type JSON_String struct {
  Str _dafny.Sequence
}

func (JSON_String) isJSON() {}

func (CompanionStruct_JSON_) Create_String_(Str _dafny.Sequence) JSON {
  return JSON{JSON_String{Str}}
}

func (_this JSON) Is_String() bool {
  _, ok := _this.Get_().(JSON_String)
  return ok
}

type JSON_Number struct {
  Num Decimal
}

func (JSON_Number) isJSON() {}

func (CompanionStruct_JSON_) Create_Number_(Num Decimal) JSON {
  return JSON{JSON_Number{Num}}
}

func (_this JSON) Is_Number() bool {
  _, ok := _this.Get_().(JSON_Number)
  return ok
}

type JSON_Object struct {
  Obj _dafny.Sequence
}

func (JSON_Object) isJSON() {}

func (CompanionStruct_JSON_) Create_Object_(Obj _dafny.Sequence) JSON {
  return JSON{JSON_Object{Obj}}
}

func (_this JSON) Is_Object() bool {
  _, ok := _this.Get_().(JSON_Object)
  return ok
}

type JSON_Array struct {
  Arr _dafny.Sequence
}

func (JSON_Array) isJSON() {}

func (CompanionStruct_JSON_) Create_Array_(Arr _dafny.Sequence) JSON {
  return JSON{JSON_Array{Arr}}
}

func (_this JSON) Is_Array() bool {
  _, ok := _this.Get_().(JSON_Array)
  return ok
}

func (CompanionStruct_JSON_) Default() JSON {
  return Companion_JSON_.Create_Null_()
}

func (_this JSON) Dtor_b() bool {
  return _this.Get_().(JSON_Bool).B
}

func (_this JSON) Dtor_str() _dafny.Sequence {
  return _this.Get_().(JSON_String).Str
}

func (_this JSON) Dtor_num() Decimal {
  return _this.Get_().(JSON_Number).Num
}

func (_this JSON) Dtor_obj() _dafny.Sequence {
  return _this.Get_().(JSON_Object).Obj
}

func (_this JSON) Dtor_arr() _dafny.Sequence {
  return _this.Get_().(JSON_Array).Arr
}

func (_this JSON) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case JSON_Null: {
      return "Values.JSON.Null"
    }
    case JSON_Bool: {
      return "Values.JSON.Bool" + "(" + _dafny.String(data.B) + ")"
    }
    case JSON_String: {
      return "Values.JSON.String" + "(" + data.Str.VerbatimString(true) + ")"
    }
    case JSON_Number: {
      return "Values.JSON.Number" + "(" + _dafny.String(data.Num) + ")"
    }
    case JSON_Object: {
      return "Values.JSON.Object" + "(" + _dafny.String(data.Obj) + ")"
    }
    case JSON_Array: {
      return "Values.JSON.Array" + "(" + _dafny.String(data.Arr) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this JSON) Equals(other JSON) bool {
  switch data1 := _this.Get_().(type) {
    case JSON_Null: {
      _, ok := other.Get_().(JSON_Null)
      return ok
    }
    case JSON_Bool: {
      data2, ok := other.Get_().(JSON_Bool)
      return ok && data1.B == data2.B
    }
    case JSON_String: {
      data2, ok := other.Get_().(JSON_String)
      return ok && data1.Str.Equals(data2.Str)
    }
    case JSON_Number: {
      data2, ok := other.Get_().(JSON_Number)
      return ok && data1.Num.Equals(data2.Num)
    }
    case JSON_Object: {
      data2, ok := other.Get_().(JSON_Object)
      return ok && data1.Obj.Equals(data2.Obj)
    }
    case JSON_Array: {
      data2, ok := other.Get_().(JSON_Array)
      return ok && data1.Arr.Equals(data2.Arr)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this JSON) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(JSON)
  return ok && _this.Equals(typed)
}

func Type_JSON_() _dafny.TypeDescriptor {
  return type_JSON_{}
}

type type_JSON_ struct {
}

func (_this type_JSON_) Default() interface{} {
  return Companion_JSON_.Default();
}

func (_this type_JSON_) String() string {
  return "Std_JSON_Values.JSON"
}
func (_this JSON) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = JSON{}

// End of datatype JSON
