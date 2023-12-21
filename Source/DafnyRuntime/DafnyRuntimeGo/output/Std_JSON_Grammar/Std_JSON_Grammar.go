// Package Std_JSON_Grammar
// Dafny module Std_JSON_Grammar compiled into Go

package Std_JSON_Grammar

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
  Std_JSON_Utils_Parsers "Std_JSON_Utils_Parsers"
  Std_JSON_Utils "Std_JSON_Utils"
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
var _ Std_JSON_Utils_Parsers.Dummy__
var _ Std_JSON_Utils.Dummy__

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
  return "Std_JSON_Grammar.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) Blank_q(b uint8) bool {
  return ((((b) == (uint8(32))) || ((b) == (uint8(9)))) || ((b) == (uint8(10)))) || ((b) == (uint8(13)))
}
func (_static *CompanionStruct_Default___) Digit_q(b uint8) bool {
  return ((uint8(_dafny.CodePoint('0'))) <= (b)) && ((b) <= (uint8(_dafny.CodePoint('9'))))
}
func (_static *CompanionStruct_Default___) NULL() _dafny.Sequence {
  return _dafny.SeqOf(uint8(_dafny.CodePoint('n')), uint8(_dafny.CodePoint('u')), uint8(_dafny.CodePoint('l')), uint8(_dafny.CodePoint('l')))
}
func (_static *CompanionStruct_Default___) TRUE() _dafny.Sequence {
  return _dafny.SeqOf(uint8(_dafny.CodePoint('t')), uint8(_dafny.CodePoint('r')), uint8(_dafny.CodePoint('u')), uint8(_dafny.CodePoint('e')))
}
func (_static *CompanionStruct_Default___) FALSE() _dafny.Sequence {
  return _dafny.SeqOf(uint8(_dafny.CodePoint('f')), uint8(_dafny.CodePoint('a')), uint8(_dafny.CodePoint('l')), uint8(_dafny.CodePoint('s')), uint8(_dafny.CodePoint('e')))
}
func (_static *CompanionStruct_Default___) DOUBLEQUOTE() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf(uint8(_dafny.CodePoint('"'))))
}
func (_static *CompanionStruct_Default___) PERIOD() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf(uint8(_dafny.CodePoint('.'))))
}
func (_static *CompanionStruct_Default___) E() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf(uint8(_dafny.CodePoint('e'))))
}
func (_static *CompanionStruct_Default___) COLON() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf(uint8(_dafny.CodePoint(':'))))
}
func (_static *CompanionStruct_Default___) COMMA() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf(uint8(_dafny.CodePoint(','))))
}
func (_static *CompanionStruct_Default___) LBRACE() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf(uint8(_dafny.CodePoint('{'))))
}
func (_static *CompanionStruct_Default___) RBRACE() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf(uint8(_dafny.CodePoint('}'))))
}
func (_static *CompanionStruct_Default___) LBRACKET() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf(uint8(_dafny.CodePoint('['))))
}
func (_static *CompanionStruct_Default___) RBRACKET() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf(uint8(_dafny.CodePoint(']'))))
}
func (_static *CompanionStruct_Default___) MINUS() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf(uint8(_dafny.CodePoint('-'))))
}
func (_static *CompanionStruct_Default___) EMPTY() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf())
}
// End of class Default__

// Definition of class Jchar
type Jchar struct {
}

func New_Jchar_() *Jchar {
  _this := Jchar{}

  return &_this
}

type CompanionStruct_Jchar_ struct {
}
var Companion_Jchar_ = CompanionStruct_Jchar_ {
}

func (*Jchar) String() string {
  return "Std_JSON_Grammar.Jchar"
}
func (_this *CompanionStruct_Jchar_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf(uint8(_dafny.CodePoint('b'))))
}
// End of class Jchar

func Type_Jchar_() _dafny.TypeDescriptor {
  return type_Jchar_{}
}

type type_Jchar_ struct {
}

func (_this type_Jchar_) Default() interface{} {
  return Companion_Jchar_.Witness()
}

func (_this type_Jchar_) String() string {
  return "Std_JSON_Grammar.Jchar"
}

// Definition of class Jquote
type Jquote struct {
}

func New_Jquote_() *Jquote {
  _this := Jquote{}

  return &_this
}

type CompanionStruct_Jquote_ struct {
}
var Companion_Jquote_ = CompanionStruct_Jquote_ {
}

func (*Jquote) String() string {
  return "Std_JSON_Grammar.Jquote"
}
func (_this *CompanionStruct_Jquote_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Companion_Default___.DOUBLEQUOTE()
}
// End of class Jquote

func Type_Jquote_() _dafny.TypeDescriptor {
  return type_Jquote_{}
}

type type_Jquote_ struct {
}

func (_this type_Jquote_) Default() interface{} {
  return Companion_Jquote_.Witness()
}

func (_this type_Jquote_) String() string {
  return "Std_JSON_Grammar.Jquote"
}

// Definition of class Jperiod
type Jperiod struct {
}

func New_Jperiod_() *Jperiod {
  _this := Jperiod{}

  return &_this
}

type CompanionStruct_Jperiod_ struct {
}
var Companion_Jperiod_ = CompanionStruct_Jperiod_ {
}

func (*Jperiod) String() string {
  return "Std_JSON_Grammar.Jperiod"
}
func (_this *CompanionStruct_Jperiod_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Companion_Default___.PERIOD()
}
// End of class Jperiod

func Type_Jperiod_() _dafny.TypeDescriptor {
  return type_Jperiod_{}
}

type type_Jperiod_ struct {
}

func (_this type_Jperiod_) Default() interface{} {
  return Companion_Jperiod_.Witness()
}

func (_this type_Jperiod_) String() string {
  return "Std_JSON_Grammar.Jperiod"
}

// Definition of class Je
type Je struct {
}

func New_Je_() *Je {
  _this := Je{}

  return &_this
}

type CompanionStruct_Je_ struct {
}
var Companion_Je_ = CompanionStruct_Je_ {
}

func (*Je) String() string {
  return "Std_JSON_Grammar.Je"
}
func (_this *CompanionStruct_Je_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Companion_Default___.E()
}
// End of class Je

func Type_Je_() _dafny.TypeDescriptor {
  return type_Je_{}
}

type type_Je_ struct {
}

func (_this type_Je_) Default() interface{} {
  return Companion_Je_.Witness()
}

func (_this type_Je_) String() string {
  return "Std_JSON_Grammar.Je"
}

// Definition of class Jcolon
type Jcolon struct {
}

func New_Jcolon_() *Jcolon {
  _this := Jcolon{}

  return &_this
}

type CompanionStruct_Jcolon_ struct {
}
var Companion_Jcolon_ = CompanionStruct_Jcolon_ {
}

func (*Jcolon) String() string {
  return "Std_JSON_Grammar.Jcolon"
}
func (_this *CompanionStruct_Jcolon_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Companion_Default___.COLON()
}
// End of class Jcolon

func Type_Jcolon_() _dafny.TypeDescriptor {
  return type_Jcolon_{}
}

type type_Jcolon_ struct {
}

func (_this type_Jcolon_) Default() interface{} {
  return Companion_Jcolon_.Witness()
}

func (_this type_Jcolon_) String() string {
  return "Std_JSON_Grammar.Jcolon"
}

// Definition of class Jcomma
type Jcomma struct {
}

func New_Jcomma_() *Jcomma {
  _this := Jcomma{}

  return &_this
}

type CompanionStruct_Jcomma_ struct {
}
var Companion_Jcomma_ = CompanionStruct_Jcomma_ {
}

func (*Jcomma) String() string {
  return "Std_JSON_Grammar.Jcomma"
}
func (_this *CompanionStruct_Jcomma_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Companion_Default___.COMMA()
}
// End of class Jcomma

func Type_Jcomma_() _dafny.TypeDescriptor {
  return type_Jcomma_{}
}

type type_Jcomma_ struct {
}

func (_this type_Jcomma_) Default() interface{} {
  return Companion_Jcomma_.Witness()
}

func (_this type_Jcomma_) String() string {
  return "Std_JSON_Grammar.Jcomma"
}

// Definition of class Jlbrace
type Jlbrace struct {
}

func New_Jlbrace_() *Jlbrace {
  _this := Jlbrace{}

  return &_this
}

type CompanionStruct_Jlbrace_ struct {
}
var Companion_Jlbrace_ = CompanionStruct_Jlbrace_ {
}

func (*Jlbrace) String() string {
  return "Std_JSON_Grammar.Jlbrace"
}
func (_this *CompanionStruct_Jlbrace_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Companion_Default___.LBRACE()
}
// End of class Jlbrace

func Type_Jlbrace_() _dafny.TypeDescriptor {
  return type_Jlbrace_{}
}

type type_Jlbrace_ struct {
}

func (_this type_Jlbrace_) Default() interface{} {
  return Companion_Jlbrace_.Witness()
}

func (_this type_Jlbrace_) String() string {
  return "Std_JSON_Grammar.Jlbrace"
}

// Definition of class Jrbrace
type Jrbrace struct {
}

func New_Jrbrace_() *Jrbrace {
  _this := Jrbrace{}

  return &_this
}

type CompanionStruct_Jrbrace_ struct {
}
var Companion_Jrbrace_ = CompanionStruct_Jrbrace_ {
}

func (*Jrbrace) String() string {
  return "Std_JSON_Grammar.Jrbrace"
}
func (_this *CompanionStruct_Jrbrace_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Companion_Default___.RBRACE()
}
// End of class Jrbrace

func Type_Jrbrace_() _dafny.TypeDescriptor {
  return type_Jrbrace_{}
}

type type_Jrbrace_ struct {
}

func (_this type_Jrbrace_) Default() interface{} {
  return Companion_Jrbrace_.Witness()
}

func (_this type_Jrbrace_) String() string {
  return "Std_JSON_Grammar.Jrbrace"
}

// Definition of class Jlbracket
type Jlbracket struct {
}

func New_Jlbracket_() *Jlbracket {
  _this := Jlbracket{}

  return &_this
}

type CompanionStruct_Jlbracket_ struct {
}
var Companion_Jlbracket_ = CompanionStruct_Jlbracket_ {
}

func (*Jlbracket) String() string {
  return "Std_JSON_Grammar.Jlbracket"
}
func (_this *CompanionStruct_Jlbracket_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Companion_Default___.LBRACKET()
}
// End of class Jlbracket

func Type_Jlbracket_() _dafny.TypeDescriptor {
  return type_Jlbracket_{}
}

type type_Jlbracket_ struct {
}

func (_this type_Jlbracket_) Default() interface{} {
  return Companion_Jlbracket_.Witness()
}

func (_this type_Jlbracket_) String() string {
  return "Std_JSON_Grammar.Jlbracket"
}

// Definition of class Jrbracket
type Jrbracket struct {
}

func New_Jrbracket_() *Jrbracket {
  _this := Jrbracket{}

  return &_this
}

type CompanionStruct_Jrbracket_ struct {
}
var Companion_Jrbracket_ = CompanionStruct_Jrbracket_ {
}

func (*Jrbracket) String() string {
  return "Std_JSON_Grammar.Jrbracket"
}
func (_this *CompanionStruct_Jrbracket_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Companion_Default___.RBRACKET()
}
// End of class Jrbracket

func Type_Jrbracket_() _dafny.TypeDescriptor {
  return type_Jrbracket_{}
}

type type_Jrbracket_ struct {
}

func (_this type_Jrbracket_) Default() interface{} {
  return Companion_Jrbracket_.Witness()
}

func (_this type_Jrbracket_) String() string {
  return "Std_JSON_Grammar.Jrbracket"
}

// Definition of class Jminus
type Jminus struct {
}

func New_Jminus_() *Jminus {
  _this := Jminus{}

  return &_this
}

type CompanionStruct_Jminus_ struct {
}
var Companion_Jminus_ = CompanionStruct_Jminus_ {
}

func (*Jminus) String() string {
  return "Std_JSON_Grammar.Jminus"
}
func (_this *CompanionStruct_Jminus_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Companion_Default___.MINUS()
}
// End of class Jminus

func Type_Jminus_() _dafny.TypeDescriptor {
  return type_Jminus_{}
}

type type_Jminus_ struct {
}

func (_this type_Jminus_) Default() interface{} {
  return Companion_Jminus_.Witness()
}

func (_this type_Jminus_) String() string {
  return "Std_JSON_Grammar.Jminus"
}

// Definition of class Jsign
type Jsign struct {
}

func New_Jsign_() *Jsign {
  _this := Jsign{}

  return &_this
}

type CompanionStruct_Jsign_ struct {
}
var Companion_Jsign_ = CompanionStruct_Jsign_ {
}

func (*Jsign) String() string {
  return "Std_JSON_Grammar.Jsign"
}
func (_this *CompanionStruct_Jsign_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Companion_Default___.EMPTY()
}
// End of class Jsign

func Type_Jsign_() _dafny.TypeDescriptor {
  return type_Jsign_{}
}

type type_Jsign_ struct {
}

func (_this type_Jsign_) Default() interface{} {
  return Companion_Jsign_.Witness()
}

func (_this type_Jsign_) String() string {
  return "Std_JSON_Grammar.Jsign"
}

// Definition of class Jblanks
type Jblanks struct {
}

func New_Jblanks_() *Jblanks {
  _this := Jblanks{}

  return &_this
}

type CompanionStruct_Jblanks_ struct {
}
var Companion_Jblanks_ = CompanionStruct_Jblanks_ {
}

func (*Jblanks) String() string {
  return "Std_JSON_Grammar.Jblanks"
}
func (_this *CompanionStruct_Jblanks_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf())
}
// End of class Jblanks

func Type_Jblanks_() _dafny.TypeDescriptor {
  return type_Jblanks_{}
}

type type_Jblanks_ struct {
}

func (_this type_Jblanks_) Default() interface{} {
  return Companion_Jblanks_.Witness()
}

func (_this type_Jblanks_) String() string {
  return "Std_JSON_Grammar.Jblanks"
}

// Definition of datatype Structural
type Structural struct {
  Data_Structural_
}

func (_this Structural) Get_() Data_Structural_ {
  return _this.Data_Structural_
}

type Data_Structural_ interface {
  isStructural()
}

type CompanionStruct_Structural_ struct {
}
var Companion_Structural_ = CompanionStruct_Structural_ {
}

type Structural_Structural struct {
  Before Std_JSON_Utils_Views_Core.View__
  T interface{}
  After Std_JSON_Utils_Views_Core.View__
}

func (Structural_Structural) isStructural() {}

func (CompanionStruct_Structural_) Create_Structural_(Before Std_JSON_Utils_Views_Core.View__, T interface{}, After Std_JSON_Utils_Views_Core.View__) Structural {
  return Structural{Structural_Structural{Before, T, After}}
}

func (_this Structural) Is_Structural() bool {
  _, ok := _this.Get_().(Structural_Structural)
  return ok
}

func (CompanionStruct_Structural_) Default(_default_T interface{}) Structural {
  return Companion_Structural_.Create_Structural_(Companion_Jblanks_.Witness(), _default_T, Companion_Jblanks_.Witness())
}

func (_this Structural) Dtor_before() Std_JSON_Utils_Views_Core.View__ {
  return _this.Get_().(Structural_Structural).Before
}

func (_this Structural) Dtor_t() interface{} {
  return _this.Get_().(Structural_Structural).T
}

func (_this Structural) Dtor_after() Std_JSON_Utils_Views_Core.View__ {
  return _this.Get_().(Structural_Structural).After
}

func (_this Structural) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case Structural_Structural: {
      return "Grammar.Structural.Structural" + "(" + _dafny.String(data.Before) + ", " + _dafny.String(data.T) + ", " + _dafny.String(data.After) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this Structural) Equals(other Structural) bool {
  switch data1 := _this.Get_().(type) {
    case Structural_Structural: {
      data2, ok := other.Get_().(Structural_Structural)
      return ok && data1.Before.Equals(data2.Before) && _dafny.AreEqual(data1.T, data2.T) && data1.After.Equals(data2.After)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this Structural) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(Structural)
  return ok && _this.Equals(typed)
}

func Type_Structural_(Type_T_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_Structural_{Type_T_}
}

type type_Structural_ struct {
  Type_T_ _dafny.TypeDescriptor
}

func (_this type_Structural_) Default() interface{} {
  Type_T_ := _this.Type_T_
  _ = Type_T_
  return Companion_Structural_.Default(Type_T_.Default());
}

func (_this type_Structural_) String() string {
  return "Std_JSON_Grammar.Structural"
}
func (_this Structural) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Structural{}

// End of datatype Structural

// Definition of datatype Maybe
type Maybe struct {
  Data_Maybe_
}

func (_this Maybe) Get_() Data_Maybe_ {
  return _this.Data_Maybe_
}

type Data_Maybe_ interface {
  isMaybe()
}

type CompanionStruct_Maybe_ struct {
}
var Companion_Maybe_ = CompanionStruct_Maybe_ {
}

type Maybe_Empty struct {
}

func (Maybe_Empty) isMaybe() {}

func (CompanionStruct_Maybe_) Create_Empty_() Maybe {
  return Maybe{Maybe_Empty{}}
}

func (_this Maybe) Is_Empty() bool {
  _, ok := _this.Get_().(Maybe_Empty)
  return ok
}

type Maybe_NonEmpty struct {
  T interface{}
}

func (Maybe_NonEmpty) isMaybe() {}

func (CompanionStruct_Maybe_) Create_NonEmpty_(T interface{}) Maybe {
  return Maybe{Maybe_NonEmpty{T}}
}

func (_this Maybe) Is_NonEmpty() bool {
  _, ok := _this.Get_().(Maybe_NonEmpty)
  return ok
}

func (CompanionStruct_Maybe_) Default() Maybe {
  return Companion_Maybe_.Create_Empty_()
}

func (_this Maybe) Dtor_t() interface{} {
  return _this.Get_().(Maybe_NonEmpty).T
}

func (_this Maybe) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case Maybe_Empty: {
      return "Grammar.Maybe.Empty"
    }
    case Maybe_NonEmpty: {
      return "Grammar.Maybe.NonEmpty" + "(" + _dafny.String(data.T) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this Maybe) Equals(other Maybe) bool {
  switch data1 := _this.Get_().(type) {
    case Maybe_Empty: {
      _, ok := other.Get_().(Maybe_Empty)
      return ok
    }
    case Maybe_NonEmpty: {
      data2, ok := other.Get_().(Maybe_NonEmpty)
      return ok && _dafny.AreEqual(data1.T, data2.T)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this Maybe) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(Maybe)
  return ok && _this.Equals(typed)
}

func Type_Maybe_() _dafny.TypeDescriptor {
  return type_Maybe_{}
}

type type_Maybe_ struct {
}

func (_this type_Maybe_) Default() interface{} {
  return Companion_Maybe_.Default();
}

func (_this type_Maybe_) String() string {
  return "Std_JSON_Grammar.Maybe"
}
func (_this Maybe) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Maybe{}

// End of datatype Maybe

// Definition of datatype Suffixed
type Suffixed struct {
  Data_Suffixed_
}

func (_this Suffixed) Get_() Data_Suffixed_ {
  return _this.Data_Suffixed_
}

type Data_Suffixed_ interface {
  isSuffixed()
}

type CompanionStruct_Suffixed_ struct {
}
var Companion_Suffixed_ = CompanionStruct_Suffixed_ {
}

type Suffixed_Suffixed struct {
  T interface{}
  Suffix Maybe
}

func (Suffixed_Suffixed) isSuffixed() {}

func (CompanionStruct_Suffixed_) Create_Suffixed_(T interface{}, Suffix Maybe) Suffixed {
  return Suffixed{Suffixed_Suffixed{T, Suffix}}
}

func (_this Suffixed) Is_Suffixed() bool {
  _, ok := _this.Get_().(Suffixed_Suffixed)
  return ok
}

func (CompanionStruct_Suffixed_) Default(_default_T interface{}) Suffixed {
  return Companion_Suffixed_.Create_Suffixed_(_default_T, Companion_Maybe_.Default())
}

func (_this Suffixed) Dtor_t() interface{} {
  return _this.Get_().(Suffixed_Suffixed).T
}

func (_this Suffixed) Dtor_suffix() Maybe {
  return _this.Get_().(Suffixed_Suffixed).Suffix
}

func (_this Suffixed) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case Suffixed_Suffixed: {
      return "Grammar.Suffixed.Suffixed" + "(" + _dafny.String(data.T) + ", " + _dafny.String(data.Suffix) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this Suffixed) Equals(other Suffixed) bool {
  switch data1 := _this.Get_().(type) {
    case Suffixed_Suffixed: {
      data2, ok := other.Get_().(Suffixed_Suffixed)
      return ok && _dafny.AreEqual(data1.T, data2.T) && data1.Suffix.Equals(data2.Suffix)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this Suffixed) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(Suffixed)
  return ok && _this.Equals(typed)
}

func Type_Suffixed_(Type_T_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_Suffixed_{Type_T_}
}

type type_Suffixed_ struct {
  Type_T_ _dafny.TypeDescriptor
}

func (_this type_Suffixed_) Default() interface{} {
  Type_T_ := _this.Type_T_
  _ = Type_T_
  return Companion_Suffixed_.Default(Type_T_.Default());
}

func (_this type_Suffixed_) String() string {
  return "Std_JSON_Grammar.Suffixed"
}
func (_this Suffixed) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Suffixed{}

// End of datatype Suffixed

// Definition of class SuffixedSequence
type SuffixedSequence struct {
}

func New_SuffixedSequence_() *SuffixedSequence {
  _this := SuffixedSequence{}

  return &_this
}

type CompanionStruct_SuffixedSequence_ struct {
}
var Companion_SuffixedSequence_ = CompanionStruct_SuffixedSequence_ {
}

func (*SuffixedSequence) String() string {
  return "Std_JSON_Grammar.SuffixedSequence"
}
// End of class SuffixedSequence

func Type_SuffixedSequence_(Type_D_ _dafny.TypeDescriptor, Type_S_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_SuffixedSequence_{Type_D_, Type_S_}
}

type type_SuffixedSequence_ struct {
  Type_D_ _dafny.TypeDescriptor
  Type_S_ _dafny.TypeDescriptor
}

func (_this type_SuffixedSequence_) Default() interface{} {
  return _dafny.EmptySeq
}

func (_this type_SuffixedSequence_) String() string {
  return "Std_JSON_Grammar.SuffixedSequence"
}

// Definition of datatype Bracketed
type Bracketed struct {
  Data_Bracketed_
}

func (_this Bracketed) Get_() Data_Bracketed_ {
  return _this.Data_Bracketed_
}

type Data_Bracketed_ interface {
  isBracketed()
}

type CompanionStruct_Bracketed_ struct {
}
var Companion_Bracketed_ = CompanionStruct_Bracketed_ {
}

type Bracketed_Bracketed struct {
  L Structural
  Data _dafny.Sequence
  R Structural
}

func (Bracketed_Bracketed) isBracketed() {}

func (CompanionStruct_Bracketed_) Create_Bracketed_(L Structural, Data _dafny.Sequence, R Structural) Bracketed {
  return Bracketed{Bracketed_Bracketed{L, Data, R}}
}

func (_this Bracketed) Is_Bracketed() bool {
  _, ok := _this.Get_().(Bracketed_Bracketed)
  return ok
}

func (CompanionStruct_Bracketed_) Default(_default_L interface{}, _default_R interface{}) Bracketed {
  return Companion_Bracketed_.Create_Bracketed_(Companion_Structural_.Default(_default_L), _dafny.EmptySeq, Companion_Structural_.Default(_default_R))
}

func (_this Bracketed) Dtor_l() Structural {
  return _this.Get_().(Bracketed_Bracketed).L
}

func (_this Bracketed) Dtor_data() _dafny.Sequence {
  return _this.Get_().(Bracketed_Bracketed).Data
}

func (_this Bracketed) Dtor_r() Structural {
  return _this.Get_().(Bracketed_Bracketed).R
}

func (_this Bracketed) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case Bracketed_Bracketed: {
      return "Grammar.Bracketed.Bracketed" + "(" + _dafny.String(data.L) + ", " + _dafny.String(data.Data) + ", " + _dafny.String(data.R) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this Bracketed) Equals(other Bracketed) bool {
  switch data1 := _this.Get_().(type) {
    case Bracketed_Bracketed: {
      data2, ok := other.Get_().(Bracketed_Bracketed)
      return ok && data1.L.Equals(data2.L) && data1.Data.Equals(data2.Data) && data1.R.Equals(data2.R)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this Bracketed) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(Bracketed)
  return ok && _this.Equals(typed)
}

func Type_Bracketed_(Type_L_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_Bracketed_{Type_L_, Type_R_}
}

type type_Bracketed_ struct {
  Type_L_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_Bracketed_) Default() interface{} {
  Type_L_ := _this.Type_L_
  _ = Type_L_
  Type_R_ := _this.Type_R_
  _ = Type_R_
  return Companion_Bracketed_.Default(Type_L_.Default(), Type_R_.Default());
}

func (_this type_Bracketed_) String() string {
  return "Std_JSON_Grammar.Bracketed"
}
func (_this Bracketed) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Bracketed{}

// End of datatype Bracketed

// Definition of class Jnull
type Jnull struct {
}

func New_Jnull_() *Jnull {
  _this := Jnull{}

  return &_this
}

type CompanionStruct_Jnull_ struct {
}
var Companion_Jnull_ = CompanionStruct_Jnull_ {
}

func (*Jnull) String() string {
  return "Std_JSON_Grammar.Jnull"
}
func (_this *CompanionStruct_Jnull_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(Companion_Default___.NULL())
}
// End of class Jnull

func Type_Jnull_() _dafny.TypeDescriptor {
  return type_Jnull_{}
}

type type_Jnull_ struct {
}

func (_this type_Jnull_) Default() interface{} {
  return Companion_Jnull_.Witness()
}

func (_this type_Jnull_) String() string {
  return "Std_JSON_Grammar.Jnull"
}

// Definition of class Jbool
type Jbool struct {
}

func New_Jbool_() *Jbool {
  _this := Jbool{}

  return &_this
}

type CompanionStruct_Jbool_ struct {
}
var Companion_Jbool_ = CompanionStruct_Jbool_ {
}

func (*Jbool) String() string {
  return "Std_JSON_Grammar.Jbool"
}
func (_this *CompanionStruct_Jbool_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(Companion_Default___.TRUE())
}
// End of class Jbool

func Type_Jbool_() _dafny.TypeDescriptor {
  return type_Jbool_{}
}

type type_Jbool_ struct {
}

func (_this type_Jbool_) Default() interface{} {
  return Companion_Jbool_.Witness()
}

func (_this type_Jbool_) String() string {
  return "Std_JSON_Grammar.Jbool"
}

// Definition of class Jdigits
type Jdigits struct {
}

func New_Jdigits_() *Jdigits {
  _this := Jdigits{}

  return &_this
}

type CompanionStruct_Jdigits_ struct {
}
var Companion_Jdigits_ = CompanionStruct_Jdigits_ {
}

func (*Jdigits) String() string {
  return "Std_JSON_Grammar.Jdigits"
}
func (_this *CompanionStruct_Jdigits_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf())
}
// End of class Jdigits

func Type_Jdigits_() _dafny.TypeDescriptor {
  return type_Jdigits_{}
}

type type_Jdigits_ struct {
}

func (_this type_Jdigits_) Default() interface{} {
  return Companion_Jdigits_.Witness()
}

func (_this type_Jdigits_) String() string {
  return "Std_JSON_Grammar.Jdigits"
}

// Definition of class Jnum
type Jnum struct {
}

func New_Jnum_() *Jnum {
  _this := Jnum{}

  return &_this
}

type CompanionStruct_Jnum_ struct {
}
var Companion_Jnum_ = CompanionStruct_Jnum_ {
}

func (*Jnum) String() string {
  return "Std_JSON_Grammar.Jnum"
}
func (_this *CompanionStruct_Jnum_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf(uint8(_dafny.CodePoint('0'))))
}
// End of class Jnum

func Type_Jnum_() _dafny.TypeDescriptor {
  return type_Jnum_{}
}

type type_Jnum_ struct {
}

func (_this type_Jnum_) Default() interface{} {
  return Companion_Jnum_.Witness()
}

func (_this type_Jnum_) String() string {
  return "Std_JSON_Grammar.Jnum"
}

// Definition of class Jint
type Jint struct {
}

func New_Jint_() *Jint {
  _this := Jint{}

  return &_this
}

type CompanionStruct_Jint_ struct {
}
var Companion_Jint_ = CompanionStruct_Jint_ {
}

func (*Jint) String() string {
  return "Std_JSON_Grammar.Jint"
}
func (_this *CompanionStruct_Jint_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf(uint8(_dafny.CodePoint('0'))))
}
// End of class Jint

func Type_Jint_() _dafny.TypeDescriptor {
  return type_Jint_{}
}

type type_Jint_ struct {
}

func (_this type_Jint_) Default() interface{} {
  return Companion_Jint_.Witness()
}

func (_this type_Jint_) String() string {
  return "Std_JSON_Grammar.Jint"
}

// Definition of class Jstr
type Jstr struct {
}

func New_Jstr_() *Jstr {
  _this := Jstr{}

  return &_this
}

type CompanionStruct_Jstr_ struct {
}
var Companion_Jstr_ = CompanionStruct_Jstr_ {
}

func (*Jstr) String() string {
  return "Std_JSON_Grammar.Jstr"
}
func (_this *CompanionStruct_Jstr_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf())
}
// End of class Jstr

func Type_Jstr_() _dafny.TypeDescriptor {
  return type_Jstr_{}
}

type type_Jstr_ struct {
}

func (_this type_Jstr_) Default() interface{} {
  return Companion_Jstr_.Witness()
}

func (_this type_Jstr_) String() string {
  return "Std_JSON_Grammar.Jstr"
}

// Definition of datatype Jstring
type Jstring struct {
  Data_Jstring_
}

func (_this Jstring) Get_() Data_Jstring_ {
  return _this.Data_Jstring_
}

type Data_Jstring_ interface {
  isJstring()
}

type CompanionStruct_Jstring_ struct {
}
var Companion_Jstring_ = CompanionStruct_Jstring_ {
}

type Jstring_JString struct {
  Lq Std_JSON_Utils_Views_Core.View__
  Contents Std_JSON_Utils_Views_Core.View__
  Rq Std_JSON_Utils_Views_Core.View__
}

func (Jstring_JString) isJstring() {}

func (CompanionStruct_Jstring_) Create_JString_(Lq Std_JSON_Utils_Views_Core.View__, Contents Std_JSON_Utils_Views_Core.View__, Rq Std_JSON_Utils_Views_Core.View__) Jstring {
  return Jstring{Jstring_JString{Lq, Contents, Rq}}
}

func (_this Jstring) Is_JString() bool {
  _, ok := _this.Get_().(Jstring_JString)
  return ok
}

func (CompanionStruct_Jstring_) Default() Jstring {
  return Companion_Jstring_.Create_JString_(Companion_Jquote_.Witness(), Companion_Jstr_.Witness(), Companion_Jquote_.Witness())
}

func (_this Jstring) Dtor_lq() Std_JSON_Utils_Views_Core.View__ {
  return _this.Get_().(Jstring_JString).Lq
}

func (_this Jstring) Dtor_contents() Std_JSON_Utils_Views_Core.View__ {
  return _this.Get_().(Jstring_JString).Contents
}

func (_this Jstring) Dtor_rq() Std_JSON_Utils_Views_Core.View__ {
  return _this.Get_().(Jstring_JString).Rq
}

func (_this Jstring) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case Jstring_JString: {
      return "Grammar.jstring.JString" + "(" + _dafny.String(data.Lq) + ", " + _dafny.String(data.Contents) + ", " + _dafny.String(data.Rq) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this Jstring) Equals(other Jstring) bool {
  switch data1 := _this.Get_().(type) {
    case Jstring_JString: {
      data2, ok := other.Get_().(Jstring_JString)
      return ok && data1.Lq.Equals(data2.Lq) && data1.Contents.Equals(data2.Contents) && data1.Rq.Equals(data2.Rq)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this Jstring) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(Jstring)
  return ok && _this.Equals(typed)
}

func Type_Jstring_() _dafny.TypeDescriptor {
  return type_Jstring_{}
}

type type_Jstring_ struct {
}

func (_this type_Jstring_) Default() interface{} {
  return Companion_Jstring_.Default();
}

func (_this type_Jstring_) String() string {
  return "Std_JSON_Grammar.Jstring"
}
func (_this Jstring) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Jstring{}

// End of datatype Jstring

// Definition of datatype JKeyValue
type JKeyValue struct {
  Data_JKeyValue_
}

func (_this JKeyValue) Get_() Data_JKeyValue_ {
  return _this.Data_JKeyValue_
}

type Data_JKeyValue_ interface {
  isJKeyValue()
}

type CompanionStruct_JKeyValue_ struct {
}
var Companion_JKeyValue_ = CompanionStruct_JKeyValue_ {
}

type JKeyValue_KeyValue struct {
  K Jstring
  Colon Structural
  V Value
}

func (JKeyValue_KeyValue) isJKeyValue() {}

func (CompanionStruct_JKeyValue_) Create_KeyValue_(K Jstring, Colon Structural, V Value) JKeyValue {
  return JKeyValue{JKeyValue_KeyValue{K, Colon, V}}
}

func (_this JKeyValue) Is_KeyValue() bool {
  _, ok := _this.Get_().(JKeyValue_KeyValue)
  return ok
}

func (CompanionStruct_JKeyValue_) Default() JKeyValue {
  return Companion_JKeyValue_.Create_KeyValue_(Companion_Jstring_.Default(), Companion_Structural_.Default(Companion_Jcolon_.Witness()), Companion_Value_.Default())
}

func (_this JKeyValue) Dtor_k() Jstring {
  return _this.Get_().(JKeyValue_KeyValue).K
}

func (_this JKeyValue) Dtor_colon() Structural {
  return _this.Get_().(JKeyValue_KeyValue).Colon
}

func (_this JKeyValue) Dtor_v() Value {
  return _this.Get_().(JKeyValue_KeyValue).V
}

func (_this JKeyValue) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case JKeyValue_KeyValue: {
      return "Grammar.jKeyValue.KeyValue" + "(" + _dafny.String(data.K) + ", " + _dafny.String(data.Colon) + ", " + _dafny.String(data.V) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this JKeyValue) Equals(other JKeyValue) bool {
  switch data1 := _this.Get_().(type) {
    case JKeyValue_KeyValue: {
      data2, ok := other.Get_().(JKeyValue_KeyValue)
      return ok && data1.K.Equals(data2.K) && data1.Colon.Equals(data2.Colon) && data1.V.Equals(data2.V)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this JKeyValue) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(JKeyValue)
  return ok && _this.Equals(typed)
}

func Type_JKeyValue_() _dafny.TypeDescriptor {
  return type_JKeyValue_{}
}

type type_JKeyValue_ struct {
}

func (_this type_JKeyValue_) Default() interface{} {
  return Companion_JKeyValue_.Default();
}

func (_this type_JKeyValue_) String() string {
  return "Std_JSON_Grammar.JKeyValue"
}
func (_this JKeyValue) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = JKeyValue{}

// End of datatype JKeyValue

// Definition of datatype Jfrac
type Jfrac struct {
  Data_Jfrac_
}

func (_this Jfrac) Get_() Data_Jfrac_ {
  return _this.Data_Jfrac_
}

type Data_Jfrac_ interface {
  isJfrac()
}

type CompanionStruct_Jfrac_ struct {
}
var Companion_Jfrac_ = CompanionStruct_Jfrac_ {
}

type Jfrac_JFrac struct {
  Period Std_JSON_Utils_Views_Core.View__
  Num Std_JSON_Utils_Views_Core.View__
}

func (Jfrac_JFrac) isJfrac() {}

func (CompanionStruct_Jfrac_) Create_JFrac_(Period Std_JSON_Utils_Views_Core.View__, Num Std_JSON_Utils_Views_Core.View__) Jfrac {
  return Jfrac{Jfrac_JFrac{Period, Num}}
}

func (_this Jfrac) Is_JFrac() bool {
  _, ok := _this.Get_().(Jfrac_JFrac)
  return ok
}

func (CompanionStruct_Jfrac_) Default() Jfrac {
  return Companion_Jfrac_.Create_JFrac_(Companion_Jperiod_.Witness(), Companion_Jnum_.Witness())
}

func (_this Jfrac) Dtor_period() Std_JSON_Utils_Views_Core.View__ {
  return _this.Get_().(Jfrac_JFrac).Period
}

func (_this Jfrac) Dtor_num() Std_JSON_Utils_Views_Core.View__ {
  return _this.Get_().(Jfrac_JFrac).Num
}

func (_this Jfrac) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case Jfrac_JFrac: {
      return "Grammar.jfrac.JFrac" + "(" + _dafny.String(data.Period) + ", " + _dafny.String(data.Num) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this Jfrac) Equals(other Jfrac) bool {
  switch data1 := _this.Get_().(type) {
    case Jfrac_JFrac: {
      data2, ok := other.Get_().(Jfrac_JFrac)
      return ok && data1.Period.Equals(data2.Period) && data1.Num.Equals(data2.Num)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this Jfrac) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(Jfrac)
  return ok && _this.Equals(typed)
}

func Type_Jfrac_() _dafny.TypeDescriptor {
  return type_Jfrac_{}
}

type type_Jfrac_ struct {
}

func (_this type_Jfrac_) Default() interface{} {
  return Companion_Jfrac_.Default();
}

func (_this type_Jfrac_) String() string {
  return "Std_JSON_Grammar.Jfrac"
}
func (_this Jfrac) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Jfrac{}

// End of datatype Jfrac

// Definition of datatype Jexp
type Jexp struct {
  Data_Jexp_
}

func (_this Jexp) Get_() Data_Jexp_ {
  return _this.Data_Jexp_
}

type Data_Jexp_ interface {
  isJexp()
}

type CompanionStruct_Jexp_ struct {
}
var Companion_Jexp_ = CompanionStruct_Jexp_ {
}

type Jexp_JExp struct {
  E Std_JSON_Utils_Views_Core.View__
  Sign Std_JSON_Utils_Views_Core.View__
  Num Std_JSON_Utils_Views_Core.View__
}

func (Jexp_JExp) isJexp() {}

func (CompanionStruct_Jexp_) Create_JExp_(E Std_JSON_Utils_Views_Core.View__, Sign Std_JSON_Utils_Views_Core.View__, Num Std_JSON_Utils_Views_Core.View__) Jexp {
  return Jexp{Jexp_JExp{E, Sign, Num}}
}

func (_this Jexp) Is_JExp() bool {
  _, ok := _this.Get_().(Jexp_JExp)
  return ok
}

func (CompanionStruct_Jexp_) Default() Jexp {
  return Companion_Jexp_.Create_JExp_(Companion_Je_.Witness(), Companion_Jsign_.Witness(), Companion_Jnum_.Witness())
}

func (_this Jexp) Dtor_e() Std_JSON_Utils_Views_Core.View__ {
  return _this.Get_().(Jexp_JExp).E
}

func (_this Jexp) Dtor_sign() Std_JSON_Utils_Views_Core.View__ {
  return _this.Get_().(Jexp_JExp).Sign
}

func (_this Jexp) Dtor_num() Std_JSON_Utils_Views_Core.View__ {
  return _this.Get_().(Jexp_JExp).Num
}

func (_this Jexp) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case Jexp_JExp: {
      return "Grammar.jexp.JExp" + "(" + _dafny.String(data.E) + ", " + _dafny.String(data.Sign) + ", " + _dafny.String(data.Num) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this Jexp) Equals(other Jexp) bool {
  switch data1 := _this.Get_().(type) {
    case Jexp_JExp: {
      data2, ok := other.Get_().(Jexp_JExp)
      return ok && data1.E.Equals(data2.E) && data1.Sign.Equals(data2.Sign) && data1.Num.Equals(data2.Num)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this Jexp) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(Jexp)
  return ok && _this.Equals(typed)
}

func Type_Jexp_() _dafny.TypeDescriptor {
  return type_Jexp_{}
}

type type_Jexp_ struct {
}

func (_this type_Jexp_) Default() interface{} {
  return Companion_Jexp_.Default();
}

func (_this type_Jexp_) String() string {
  return "Std_JSON_Grammar.Jexp"
}
func (_this Jexp) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Jexp{}

// End of datatype Jexp

// Definition of datatype Jnumber
type Jnumber struct {
  Data_Jnumber_
}

func (_this Jnumber) Get_() Data_Jnumber_ {
  return _this.Data_Jnumber_
}

type Data_Jnumber_ interface {
  isJnumber()
}

type CompanionStruct_Jnumber_ struct {
}
var Companion_Jnumber_ = CompanionStruct_Jnumber_ {
}

type Jnumber_JNumber struct {
  Minus Std_JSON_Utils_Views_Core.View__
  Num Std_JSON_Utils_Views_Core.View__
  Frac Maybe
  Exp Maybe
}

func (Jnumber_JNumber) isJnumber() {}

func (CompanionStruct_Jnumber_) Create_JNumber_(Minus Std_JSON_Utils_Views_Core.View__, Num Std_JSON_Utils_Views_Core.View__, Frac Maybe, Exp Maybe) Jnumber {
  return Jnumber{Jnumber_JNumber{Minus, Num, Frac, Exp}}
}

func (_this Jnumber) Is_JNumber() bool {
  _, ok := _this.Get_().(Jnumber_JNumber)
  return ok
}

func (CompanionStruct_Jnumber_) Default() Jnumber {
  return Companion_Jnumber_.Create_JNumber_(Companion_Jminus_.Witness(), Companion_Jnum_.Witness(), Companion_Maybe_.Default(), Companion_Maybe_.Default())
}

func (_this Jnumber) Dtor_minus() Std_JSON_Utils_Views_Core.View__ {
  return _this.Get_().(Jnumber_JNumber).Minus
}

func (_this Jnumber) Dtor_num() Std_JSON_Utils_Views_Core.View__ {
  return _this.Get_().(Jnumber_JNumber).Num
}

func (_this Jnumber) Dtor_frac() Maybe {
  return _this.Get_().(Jnumber_JNumber).Frac
}

func (_this Jnumber) Dtor_exp() Maybe {
  return _this.Get_().(Jnumber_JNumber).Exp
}

func (_this Jnumber) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case Jnumber_JNumber: {
      return "Grammar.jnumber.JNumber" + "(" + _dafny.String(data.Minus) + ", " + _dafny.String(data.Num) + ", " + _dafny.String(data.Frac) + ", " + _dafny.String(data.Exp) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this Jnumber) Equals(other Jnumber) bool {
  switch data1 := _this.Get_().(type) {
    case Jnumber_JNumber: {
      data2, ok := other.Get_().(Jnumber_JNumber)
      return ok && data1.Minus.Equals(data2.Minus) && data1.Num.Equals(data2.Num) && data1.Frac.Equals(data2.Frac) && data1.Exp.Equals(data2.Exp)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this Jnumber) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(Jnumber)
  return ok && _this.Equals(typed)
}

func Type_Jnumber_() _dafny.TypeDescriptor {
  return type_Jnumber_{}
}

type type_Jnumber_ struct {
}

func (_this type_Jnumber_) Default() interface{} {
  return Companion_Jnumber_.Default();
}

func (_this type_Jnumber_) String() string {
  return "Std_JSON_Grammar.Jnumber"
}
func (_this Jnumber) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Jnumber{}

// End of datatype Jnumber

// Definition of datatype Value
type Value struct {
  Data_Value_
}

func (_this Value) Get_() Data_Value_ {
  return _this.Data_Value_
}

type Data_Value_ interface {
  isValue()
}

type CompanionStruct_Value_ struct {
}
var Companion_Value_ = CompanionStruct_Value_ {
}

type Value_Null struct {
  N Std_JSON_Utils_Views_Core.View__
}

func (Value_Null) isValue() {}

func (CompanionStruct_Value_) Create_Null_(N Std_JSON_Utils_Views_Core.View__) Value {
  return Value{Value_Null{N}}
}

func (_this Value) Is_Null() bool {
  _, ok := _this.Get_().(Value_Null)
  return ok
}

type Value_Bool struct {
  B Std_JSON_Utils_Views_Core.View__
}

func (Value_Bool) isValue() {}

func (CompanionStruct_Value_) Create_Bool_(B Std_JSON_Utils_Views_Core.View__) Value {
  return Value{Value_Bool{B}}
}

func (_this Value) Is_Bool() bool {
  _, ok := _this.Get_().(Value_Bool)
  return ok
}

type Value_String struct {
  Str Jstring
}

func (Value_String) isValue() {}

func (CompanionStruct_Value_) Create_String_(Str Jstring) Value {
  return Value{Value_String{Str}}
}

func (_this Value) Is_String() bool {
  _, ok := _this.Get_().(Value_String)
  return ok
}

type Value_Number struct {
  Num Jnumber
}

func (Value_Number) isValue() {}

func (CompanionStruct_Value_) Create_Number_(Num Jnumber) Value {
  return Value{Value_Number{Num}}
}

func (_this Value) Is_Number() bool {
  _, ok := _this.Get_().(Value_Number)
  return ok
}

type Value_Object struct {
  Obj Bracketed
}

func (Value_Object) isValue() {}

func (CompanionStruct_Value_) Create_Object_(Obj Bracketed) Value {
  return Value{Value_Object{Obj}}
}

func (_this Value) Is_Object() bool {
  _, ok := _this.Get_().(Value_Object)
  return ok
}

type Value_Array struct {
  Arr Bracketed
}

func (Value_Array) isValue() {}

func (CompanionStruct_Value_) Create_Array_(Arr Bracketed) Value {
  return Value{Value_Array{Arr}}
}

func (_this Value) Is_Array() bool {
  _, ok := _this.Get_().(Value_Array)
  return ok
}

func (CompanionStruct_Value_) Default() Value {
  return Companion_Value_.Create_Null_(Companion_Jnull_.Witness())
}

func (_this Value) Dtor_n() Std_JSON_Utils_Views_Core.View__ {
  return _this.Get_().(Value_Null).N
}

func (_this Value) Dtor_b() Std_JSON_Utils_Views_Core.View__ {
  return _this.Get_().(Value_Bool).B
}

func (_this Value) Dtor_str() Jstring {
  return _this.Get_().(Value_String).Str
}

func (_this Value) Dtor_num() Jnumber {
  return _this.Get_().(Value_Number).Num
}

func (_this Value) Dtor_obj() Bracketed {
  return _this.Get_().(Value_Object).Obj
}

func (_this Value) Dtor_arr() Bracketed {
  return _this.Get_().(Value_Array).Arr
}

func (_this Value) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case Value_Null: {
      return "Grammar.Value.Null" + "(" + _dafny.String(data.N) + ")"
    }
    case Value_Bool: {
      return "Grammar.Value.Bool" + "(" + _dafny.String(data.B) + ")"
    }
    case Value_String: {
      return "Grammar.Value.String" + "(" + _dafny.String(data.Str) + ")"
    }
    case Value_Number: {
      return "Grammar.Value.Number" + "(" + _dafny.String(data.Num) + ")"
    }
    case Value_Object: {
      return "Grammar.Value.Object" + "(" + _dafny.String(data.Obj) + ")"
    }
    case Value_Array: {
      return "Grammar.Value.Array" + "(" + _dafny.String(data.Arr) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this Value) Equals(other Value) bool {
  switch data1 := _this.Get_().(type) {
    case Value_Null: {
      data2, ok := other.Get_().(Value_Null)
      return ok && data1.N.Equals(data2.N)
    }
    case Value_Bool: {
      data2, ok := other.Get_().(Value_Bool)
      return ok && data1.B.Equals(data2.B)
    }
    case Value_String: {
      data2, ok := other.Get_().(Value_String)
      return ok && data1.Str.Equals(data2.Str)
    }
    case Value_Number: {
      data2, ok := other.Get_().(Value_Number)
      return ok && data1.Num.Equals(data2.Num)
    }
    case Value_Object: {
      data2, ok := other.Get_().(Value_Object)
      return ok && data1.Obj.Equals(data2.Obj)
    }
    case Value_Array: {
      data2, ok := other.Get_().(Value_Array)
      return ok && data1.Arr.Equals(data2.Arr)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this Value) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(Value)
  return ok && _this.Equals(typed)
}

func Type_Value_() _dafny.TypeDescriptor {
  return type_Value_{}
}

type type_Value_ struct {
}

func (_this type_Value_) Default() interface{} {
  return Companion_Value_.Default();
}

func (_this type_Value_) String() string {
  return "Std_JSON_Grammar.Value"
}
func (_this Value) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Value{}

// End of datatype Value
