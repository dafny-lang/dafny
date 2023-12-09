// Package Std_JSON_ZeroCopy_Deserializer_Strings
// Dafny module Std_JSON_ZeroCopy_Deserializer_Strings compiled into Go

package Std_JSON_ZeroCopy_Deserializer_Strings

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
  Std_JSON_ZeroCopy_Deserializer_Core "Std_JSON_ZeroCopy_Deserializer_Core"
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
var _ Std_JSON_ZeroCopy_Deserializer_Core.Dummy__

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
  return "Std_JSON_ZeroCopy_Deserializer_Strings.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) StringBody(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  var pr Std_Wrappers.Result = Std_Wrappers.Companion_Result_.Default(Std_JSON_Utils_Cursors.Companion_Cursor_.Witness())
  _ = pr
  var _614_escaped bool
  _ = _614_escaped
  _614_escaped = false
  var _hi3 uint32 = (cs).Dtor_end()
  _ = _hi3
  for _615_point_k := (cs).Dtor_point(); _615_point_k < _hi3; _615_point_k++ {
    var _616_byte uint8
    _ = _616_byte
    _616_byte = ((cs).Dtor_s()).Select(uint32(_615_point_k)).(uint8)
    if (((_616_byte) == (uint8(_dafny.CodePoint('"')))) && (!(_614_escaped))) {
      pr = Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Utils_Cursors.Companion_Cursor___.Create_Cursor_((cs).Dtor_s(), (cs).Dtor_beg(), _615_point_k, (cs).Dtor_end()))
      return pr
    } else if ((_616_byte) == (uint8(_dafny.CodePoint('\\')))) {
      _614_escaped = !(_614_escaped)
    } else {
      _614_escaped = false
    }
  }
  pr = Std_Wrappers.Companion_Result_.Create_Failure_(Std_JSON_Utils_Cursors.Companion_CursorError_.Create_EOF_())
  return pr
  return pr
}
func (_static *CompanionStruct_Default___) Quote(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  var _617_valueOrError0 Std_Wrappers.Result = (cs).AssertChar(_dafny.CodePoint('"'))
  _ = _617_valueOrError0
  if ((_617_valueOrError0).IsFailure()) {
    return (_617_valueOrError0).PropagateFailure()
  } else {
    var _618_cs Std_JSON_Utils_Cursors.Cursor__ = (_617_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Cursor__)
    _ = _618_cs
    return Std_Wrappers.Companion_Result_.Create_Success_((_618_cs).Split())
  }
}
func (_static *CompanionStruct_Default___) String(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  var _619_valueOrError0 Std_Wrappers.Result = Companion_Default___.Quote(cs)
  _ = _619_valueOrError0
  if ((_619_valueOrError0).IsFailure()) {
    return (_619_valueOrError0).PropagateFailure()
  } else {
    var _let_tmp_rhs24 Std_JSON_Utils_Cursors.Split = (_619_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Split)
    _ = _let_tmp_rhs24
    var _620_lq Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs24.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
    _ = _620_lq
    var _621_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs24.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
    _ = _621_cs
    var _622_valueOrError1 Std_Wrappers.Result = Companion_Default___.StringBody(_621_cs)
    _ = _622_valueOrError1
    if ((_622_valueOrError1).IsFailure()) {
      return (_622_valueOrError1).PropagateFailure()
    } else {
      var _623_contents Std_JSON_Utils_Cursors.Cursor__ = (_622_valueOrError1).Extract().(Std_JSON_Utils_Cursors.Cursor__)
      _ = _623_contents
      var _let_tmp_rhs25 Std_JSON_Utils_Cursors.Split = (_623_contents).Split()
      _ = _let_tmp_rhs25
      var _624_contents Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs25.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
      _ = _624_contents
      var _625_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs25.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
      _ = _625_cs
      var _626_valueOrError2 Std_Wrappers.Result = Companion_Default___.Quote(_625_cs)
      _ = _626_valueOrError2
      if ((_626_valueOrError2).IsFailure()) {
        return (_626_valueOrError2).PropagateFailure()
      } else {
        var _let_tmp_rhs26 Std_JSON_Utils_Cursors.Split = (_626_valueOrError2).Extract().(Std_JSON_Utils_Cursors.Split)
        _ = _let_tmp_rhs26
        var _627_rq Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs26.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
        _ = _627_rq
        var _628_cs Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs26.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
        _ = _628_cs
        return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(Std_JSON_Grammar.Companion_Jstring_.Create_JString_(_620_lq, _624_contents, _627_rq), _628_cs))
      }
    }
  }
}
// End of class Default__
