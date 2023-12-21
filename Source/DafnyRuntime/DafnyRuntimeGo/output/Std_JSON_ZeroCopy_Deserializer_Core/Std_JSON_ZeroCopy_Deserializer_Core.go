// Package Std_JSON_ZeroCopy_Deserializer_Core
// Dafny module Std_JSON_ZeroCopy_Deserializer_Core compiled into Go

package Std_JSON_ZeroCopy_Deserializer_Core

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
  Std_JSON_Grammar "Std_JSON_Grammar"
  Std_JSON_ByteStrConversion "Std_JSON_ByteStrConversion"
  Std_JSON_Serializer "Std_JSON_Serializer"
  Std_JSON_Deserializer_Uint16StrConversion "Std_JSON_Deserializer_Uint16StrConversion"
  Std_JSON_Deserializer "Std_JSON_Deserializer"
  Std_JSON_ConcreteSyntax_Spec "Std_JSON_ConcreteSyntax_Spec"
  Std_JSON_ConcreteSyntax_SpecProperties "Std_JSON_ConcreteSyntax_SpecProperties"
  Std_JSON_ConcreteSyntax "Std_JSON_ConcreteSyntax"
  Std_JSON_ZeroCopy_Serializer "Std_JSON_ZeroCopy_Serializer"
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
var _ Std_JSON_Grammar.Dummy__
var _ Std_JSON_ByteStrConversion.Dummy__
var _ Std_JSON_Serializer.Dummy__
var _ Std_JSON_Deserializer_Uint16StrConversion.Dummy__
var _ Std_JSON_Deserializer.Dummy__
var _ Std_JSON_ConcreteSyntax_Spec.Dummy__
var _ Std_JSON_ConcreteSyntax_SpecProperties.Dummy__
var _ Std_JSON_ConcreteSyntax.Dummy__
var _ Std_JSON_ZeroCopy_Serializer.Dummy__

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
  return "Std_JSON_ZeroCopy_Deserializer_Core.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) Get(cs Std_JSON_Utils_Cursors.Cursor__, err Std_JSON_Errors.DeserializationError) Std_Wrappers.Result {
  var _604_valueOrError0 Std_Wrappers.Result = (cs).Get(err)
  _ = _604_valueOrError0
  if ((_604_valueOrError0).IsFailure()) {
    return (_604_valueOrError0).PropagateFailure()
  } else {
    var _605_cs Std_JSON_Utils_Cursors.Cursor__ = (_604_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Cursor__)
    _ = _605_cs
    return Std_Wrappers.Companion_Result_.Create_Success_((_605_cs).Split())
  }
}
func (_static *CompanionStruct_Default___) WS(cs Std_JSON_Utils_Cursors.Cursor__) Std_JSON_Utils_Cursors.Split {
  var sp Std_JSON_Utils_Cursors.Split = Std_JSON_Utils_Cursors.Companion_Split_.Default(Std_JSON_Grammar.Companion_Jblanks_.Witness())
  _ = sp
  var _606_point_k uint32
  _ = _606_point_k
  _606_point_k = (cs).Dtor_point()
  var _607_end uint32
  _ = _607_end
  _607_end = (cs).Dtor_end()
  for ((_606_point_k) < (_607_end)) && (Std_JSON_Grammar.Companion_Default___.Blank_q(((cs).Dtor_s()).Select(uint32(_606_point_k)).(uint8))) {
    _606_point_k = (_606_point_k) + (uint32(1))
  }
  sp = (Std_JSON_Utils_Cursors.Companion_Cursor___.Create_Cursor_((cs).Dtor_s(), (cs).Dtor_beg(), _606_point_k, (cs).Dtor_end())).Split()
  return sp
  return sp
}
func (_static *CompanionStruct_Default___) Structural(cs Std_JSON_Utils_Cursors.Cursor__, parser func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result) Std_Wrappers.Result {
  var _let_tmp_rhs18 Std_JSON_Utils_Cursors.Split = Companion_Default___.WS(cs)
  _ = _let_tmp_rhs18
  var _608_before Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs18.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
  _ = _608_before
  var _609_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs18.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
  _ = _609_cs
  var _610_valueOrError0 Std_Wrappers.Result = ((parser))(_609_cs)
  _ = _610_valueOrError0
  if ((_610_valueOrError0).IsFailure()) {
    return (_610_valueOrError0).PropagateFailure()
  } else {
    var _let_tmp_rhs19 Std_JSON_Utils_Cursors.Split = (_610_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Split)
    _ = _let_tmp_rhs19
    var _611_val interface{} = _let_tmp_rhs19.Get_().(Std_JSON_Utils_Cursors.Split_SP).T
    _ = _611_val
    var _612_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs19.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
    _ = _612_cs
    var _let_tmp_rhs20 Std_JSON_Utils_Cursors.Split = Companion_Default___.WS(_612_cs)
    _ = _let_tmp_rhs20
    var _613_after Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs20.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
    _ = _613_after
    var _614_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs20.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
    _ = _614_cs
    return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(Std_JSON_Grammar.Companion_Structural_.Create_Structural_(_608_before, _611_val, _613_after), _614_cs))
  }
}
func (_static *CompanionStruct_Default___) TryStructural(cs Std_JSON_Utils_Cursors.Cursor__) Std_JSON_Utils_Cursors.Split {
  var _let_tmp_rhs21 Std_JSON_Utils_Cursors.Split = Companion_Default___.WS(cs)
  _ = _let_tmp_rhs21
  var _615_before Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs21.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
  _ = _615_before
  var _616_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs21.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
  _ = _616_cs
  var _let_tmp_rhs22 Std_JSON_Utils_Cursors.Split = ((_616_cs).SkipByte()).Split()
  _ = _let_tmp_rhs22
  var _617_val Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs22.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
  _ = _617_val
  var _618_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs22.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
  _ = _618_cs
  var _let_tmp_rhs23 Std_JSON_Utils_Cursors.Split = Companion_Default___.WS(_618_cs)
  _ = _let_tmp_rhs23
  var _619_after Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs23.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
  _ = _619_after
  var _620_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs23.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
  _ = _620_cs
  return Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(Std_JSON_Grammar.Companion_Structural_.Create_Structural_(_615_before, _617_val, _619_after), _620_cs)
}
func (_static *CompanionStruct_Default___) SpecView() func (Std_JSON_Utils_Views_Core.View__) _dafny.Sequence {
  return func (_621_v Std_JSON_Utils_Views_Core.View__) _dafny.Sequence {
    return Std_JSON_ConcreteSyntax_Spec.Companion_Default___.View(_621_v)
  }
}
// End of class Default__

// Definition of class Jopt
type Jopt struct {
}

func New_Jopt_() *Jopt {
  _this := Jopt{}

  return &_this
}

type CompanionStruct_Jopt_ struct {
}
var Companion_Jopt_ = CompanionStruct_Jopt_ {
}

func (*Jopt) String() string {
  return "Std_JSON_ZeroCopy_Deserializer_Core.Jopt"
}
func (_this *CompanionStruct_Jopt_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf())
}
// End of class Jopt

func Type_Jopt_() _dafny.TypeDescriptor {
  return type_Jopt_{}
}

type type_Jopt_ struct {
}

func (_this type_Jopt_) Default() interface{} {
  return Companion_Jopt_.Witness()
}

func (_this type_Jopt_) String() string {
  return "Std_JSON_ZeroCopy_Deserializer_Core.Jopt"
}

// Definition of class ValueParser
type ValueParser struct {
}

func New_ValueParser_() *ValueParser {
  _this := ValueParser{}

  return &_this
}

type CompanionStruct_ValueParser_ struct {
}
var Companion_ValueParser_ = CompanionStruct_ValueParser_ {
}

func (*ValueParser) String() string {
  return "Std_JSON_ZeroCopy_Deserializer_Core.ValueParser"
}
// End of class ValueParser

func Type_ValueParser_() _dafny.TypeDescriptor {
  return type_ValueParser_{}
}

type type_ValueParser_ struct {
}

func (_this type_ValueParser_) Default() interface{} {
  return Std_JSON_Utils_Parsers.Companion_SubParser_.Witness()
}

func (_this type_ValueParser_) String() string {
  return "Std_JSON_ZeroCopy_Deserializer_Core.ValueParser"
}
