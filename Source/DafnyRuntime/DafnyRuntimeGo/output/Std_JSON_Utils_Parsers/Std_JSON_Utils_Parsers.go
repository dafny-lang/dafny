// Package Std_JSON_Utils_Parsers
// Dafny module Std_JSON_Utils_Parsers compiled into Go

package Std_JSON_Utils_Parsers

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
  return "Std_JSON_Utils_Parsers.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) ParserWitness() func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  return func (_398___v9 Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
    return Std_Wrappers.Companion_Result_.Create_Failure_(Std_JSON_Utils_Cursors.Companion_CursorError_.Create_EOF_())
  }
}
func (_static *CompanionStruct_Default___) SubParserWitness() func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  return func (_399_cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
    return Std_Wrappers.Companion_Result_.Create_Failure_(Std_JSON_Utils_Cursors.Companion_CursorError_.Create_EOF_())
  }
}
// End of class Default__

// Definition of class Parser
type Parser struct {
}

func New_Parser_() *Parser {
  _this := Parser{}

  return &_this
}

type CompanionStruct_Parser_ struct {
}
var Companion_Parser_ = CompanionStruct_Parser_ {
}

func (*Parser) String() string {
  return "Std_JSON_Utils_Parsers.Parser"
}
func (_this *CompanionStruct_Parser_) Witness() func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  return func (coer30 func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result) func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  return func (arg32 Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
    return coer30(arg32)
  }
}(Companion_Default___.ParserWitness())
}
// End of class Parser

func Type_Parser_(Type_T_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_Parser_{Type_T_, Type_R_}
}

type type_Parser_ struct {
  Type_T_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_Parser_) Default() interface{} {
  return Companion_Parser_.Witness()
}

func (_this type_Parser_) String() string {
  return "Std_JSON_Utils_Parsers.Parser"
}

// Definition of datatype Parser__
type Parser__ struct {
  Data_Parser___
}

func (_this Parser__) Get_() Data_Parser___ {
  return _this.Data_Parser___
}

type Data_Parser___ interface {
  isParser__()
}

type CompanionStruct_Parser___ struct {
}
var Companion_Parser___ = CompanionStruct_Parser___ {
}

type Parser___Parser struct {
  Fn func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result
}

func (Parser___Parser) isParser__() {}

func (CompanionStruct_Parser___) Create_Parser_(Fn func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result) Parser__ {
  return Parser__{Parser___Parser{Fn}}
}

func (_this Parser__) Is_Parser() bool {
  _, ok := _this.Get_().(Parser___Parser)
  return ok
}

func (CompanionStruct_Parser___) Default(_default_T interface{}) func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  return func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result { return Std_Wrappers.Companion_Result_.Default(Std_JSON_Utils_Cursors.Companion_Split_.Default(_default_T)); }
}

func (_this Parser__) Dtor_fn() func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  return _this.Get_().(Parser___Parser).Fn
}

func (_this Parser__) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case Parser___Parser: {
      return "Parsers.Parser_.Parser" + "(" + _dafny.String(data.Fn) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this Parser__) Equals(other Parser__) bool {
  switch data1 := _this.Get_().(type) {
    case Parser___Parser: {
      data2, ok := other.Get_().(Parser___Parser)
      return ok && _dafny.AreEqual(data1.Fn, data2.Fn)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this Parser__) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(Parser__)
  return ok && _this.Equals(typed)
}

func Type_Parser___(Type_T_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_Parser___{Type_T_}
}

type type_Parser___ struct {
  Type_T_ _dafny.TypeDescriptor
}

func (_this type_Parser___) Default() interface{} {
  Type_T_ := _this.Type_T_
  _ = Type_T_
  return Companion_Parser___.Default(Type_T_.Default());
}

func (_this type_Parser___) String() string {
  return "Std_JSON_Utils_Parsers.Parser__"
}
func (_this Parser__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Parser__{}

// End of datatype Parser__

// Definition of datatype SubParser__
type SubParser__ struct {
  Data_SubParser___
}

func (_this SubParser__) Get_() Data_SubParser___ {
  return _this.Data_SubParser___
}

type Data_SubParser___ interface {
  isSubParser__()
}

type CompanionStruct_SubParser___ struct {
}
var Companion_SubParser___ = CompanionStruct_SubParser___ {
}

type SubParser___SubParser struct {
  Fn func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result
}

func (SubParser___SubParser) isSubParser__() {}

func (CompanionStruct_SubParser___) Create_SubParser_(Fn func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result) SubParser__ {
  return SubParser__{SubParser___SubParser{Fn}}
}

func (_this SubParser__) Is_SubParser() bool {
  _, ok := _this.Get_().(SubParser___SubParser)
  return ok
}

func (CompanionStruct_SubParser___) Default() func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  return (func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result)(nil)
}

func (_this SubParser__) Dtor_fn() func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  return _this.Get_().(SubParser___SubParser).Fn
}

func (_this SubParser__) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case SubParser___SubParser: {
      return "Parsers.SubParser_.SubParser" + "(" + _dafny.String(data.Fn) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this SubParser__) Equals(other SubParser__) bool {
  switch data1 := _this.Get_().(type) {
    case SubParser___SubParser: {
      data2, ok := other.Get_().(SubParser___SubParser)
      return ok && _dafny.AreEqual(data1.Fn, data2.Fn)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this SubParser__) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(SubParser__)
  return ok && _this.Equals(typed)
}

func Type_SubParser___() _dafny.TypeDescriptor {
  return type_SubParser___{}
}

type type_SubParser___ struct {
}

func (_this type_SubParser___) Default() interface{} {
  return Companion_SubParser___.Default();
}

func (_this type_SubParser___) String() string {
  return "Std_JSON_Utils_Parsers.SubParser__"
}
func (_this SubParser__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = SubParser__{}

// End of datatype SubParser__

// Definition of class SubParser
type SubParser struct {
}

func New_SubParser_() *SubParser {
  _this := SubParser{}

  return &_this
}

type CompanionStruct_SubParser_ struct {
}
var Companion_SubParser_ = CompanionStruct_SubParser_ {
}

func (*SubParser) String() string {
  return "Std_JSON_Utils_Parsers.SubParser"
}
func (_this *CompanionStruct_SubParser_) Witness() func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  return func (coer31 func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result) func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  return func (arg33 Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
    return coer31(arg33)
  }
}(Companion_Default___.SubParserWitness())
}
// End of class SubParser

func Type_SubParser_(Type_T_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_SubParser_{Type_T_, Type_R_}
}

type type_SubParser_ struct {
  Type_T_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_SubParser_) Default() interface{} {
  return Companion_SubParser_.Witness()
}

func (_this type_SubParser_) String() string {
  return "Std_JSON_Utils_Parsers.SubParser"
}
