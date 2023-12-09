// Package Std_JSON_ZeroCopy_Deserializer_Values
// Dafny module Std_JSON_ZeroCopy_Deserializer_Values compiled into Go

package Std_JSON_ZeroCopy_Deserializer_Values

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
  Std_JSON_ZeroCopy_Deserializer_Strings "Std_JSON_ZeroCopy_Deserializer_Strings"
  Std_JSON_ZeroCopy_Deserializer_Numbers "Std_JSON_ZeroCopy_Deserializer_Numbers"
  Std_JSON_ZeroCopy_Deserializer_ObjectParams "Std_JSON_ZeroCopy_Deserializer_ObjectParams"
  Std_JSON_ZeroCopy_Deserializer_Objects "Std_JSON_ZeroCopy_Deserializer_Objects"
  Std_JSON_ZeroCopy_Deserializer_ArrayParams "Std_JSON_ZeroCopy_Deserializer_ArrayParams"
  Std_JSON_ZeroCopy_Deserializer_Arrays "Std_JSON_ZeroCopy_Deserializer_Arrays"
  Std_JSON_ZeroCopy_Deserializer_Constants "Std_JSON_ZeroCopy_Deserializer_Constants"
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
var _ Std_JSON_ZeroCopy_Deserializer_Strings.Dummy__
var _ Std_JSON_ZeroCopy_Deserializer_Numbers.Dummy__
var _ Std_JSON_ZeroCopy_Deserializer_ObjectParams.Dummy__
var _ Std_JSON_ZeroCopy_Deserializer_Objects.Dummy__
var _ Std_JSON_ZeroCopy_Deserializer_ArrayParams.Dummy__
var _ Std_JSON_ZeroCopy_Deserializer_Arrays.Dummy__
var _ Std_JSON_ZeroCopy_Deserializer_Constants.Dummy__

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
  return "Std_JSON_ZeroCopy_Deserializer_Values.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) Value(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  var _725_c int16 = (cs).Peek()
  _ = _725_c
  if ((_725_c) == (int16(_dafny.CodePoint('{')))) {
    var _726_valueOrError0 Std_Wrappers.Result = Std_JSON_ZeroCopy_Deserializer_Objects.Companion_Default___.Object(cs, Companion_Default___.ValueParser(cs))
    _ = _726_valueOrError0
    if ((_726_valueOrError0).IsFailure()) {
      return (_726_valueOrError0).PropagateFailure()
    } else {
      var _let_tmp_rhs32 Std_JSON_Utils_Cursors.Split = (_726_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Split)
      _ = _let_tmp_rhs32
      var _727_obj Std_JSON_Grammar.Bracketed = _let_tmp_rhs32.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Grammar.Bracketed)
      _ = _727_obj
      var _728_cs_k Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs32.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
      _ = _728_cs_k
      var _729_v Std_JSON_Grammar.Value = Std_JSON_Grammar.Companion_Value_.Create_Object_(_727_obj)
      _ = _729_v
      var _730_sp Std_JSON_Utils_Cursors.Split = Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(_729_v, _728_cs_k)
      _ = _730_sp
      return Std_Wrappers.Companion_Result_.Create_Success_(_730_sp)
    }
  } else if ((_725_c) == (int16(_dafny.CodePoint('[')))) {
    var _731_valueOrError1 Std_Wrappers.Result = Std_JSON_ZeroCopy_Deserializer_Arrays.Companion_Default___.Array(cs, Companion_Default___.ValueParser(cs))
    _ = _731_valueOrError1
    if ((_731_valueOrError1).IsFailure()) {
      return (_731_valueOrError1).PropagateFailure()
    } else {
      var _let_tmp_rhs33 Std_JSON_Utils_Cursors.Split = (_731_valueOrError1).Extract().(Std_JSON_Utils_Cursors.Split)
      _ = _let_tmp_rhs33
      var _732_arr Std_JSON_Grammar.Bracketed = _let_tmp_rhs33.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Grammar.Bracketed)
      _ = _732_arr
      var _733_cs_k Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs33.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
      _ = _733_cs_k
      var _734_v Std_JSON_Grammar.Value = Std_JSON_Grammar.Companion_Value_.Create_Array_(_732_arr)
      _ = _734_v
      var _735_sp Std_JSON_Utils_Cursors.Split = Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(_734_v, _733_cs_k)
      _ = _735_sp
      return Std_Wrappers.Companion_Result_.Create_Success_(_735_sp)
    }
  } else if ((_725_c) == (int16(_dafny.CodePoint('"')))) {
    var _736_valueOrError2 Std_Wrappers.Result = Std_JSON_ZeroCopy_Deserializer_Strings.Companion_Default___.String(cs)
    _ = _736_valueOrError2
    if ((_736_valueOrError2).IsFailure()) {
      return (_736_valueOrError2).PropagateFailure()
    } else {
      var _let_tmp_rhs34 Std_JSON_Utils_Cursors.Split = (_736_valueOrError2).Extract().(Std_JSON_Utils_Cursors.Split)
      _ = _let_tmp_rhs34
      var _737_str Std_JSON_Grammar.Jstring = _let_tmp_rhs34.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Grammar.Jstring)
      _ = _737_str
      var _738_cs_k Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs34.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
      _ = _738_cs_k
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(Std_JSON_Grammar.Companion_Value_.Create_String_(_737_str), _738_cs_k))
    }
  } else if ((_725_c) == (int16(_dafny.CodePoint('t')))) {
    var _739_valueOrError3 Std_Wrappers.Result = Std_JSON_ZeroCopy_Deserializer_Constants.Companion_Default___.Constant(cs, Std_JSON_Grammar.Companion_Default___.TRUE())
    _ = _739_valueOrError3
    if ((_739_valueOrError3).IsFailure()) {
      return (_739_valueOrError3).PropagateFailure()
    } else {
      var _let_tmp_rhs35 Std_JSON_Utils_Cursors.Split = (_739_valueOrError3).Extract().(Std_JSON_Utils_Cursors.Split)
      _ = _let_tmp_rhs35
      var _740_cst Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs35.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
      _ = _740_cst
      var _741_cs_k Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs35.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
      _ = _741_cs_k
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(Std_JSON_Grammar.Companion_Value_.Create_Bool_(_740_cst), _741_cs_k))
    }
  } else if ((_725_c) == (int16(_dafny.CodePoint('f')))) {
    var _742_valueOrError4 Std_Wrappers.Result = Std_JSON_ZeroCopy_Deserializer_Constants.Companion_Default___.Constant(cs, Std_JSON_Grammar.Companion_Default___.FALSE())
    _ = _742_valueOrError4
    if ((_742_valueOrError4).IsFailure()) {
      return (_742_valueOrError4).PropagateFailure()
    } else {
      var _let_tmp_rhs36 Std_JSON_Utils_Cursors.Split = (_742_valueOrError4).Extract().(Std_JSON_Utils_Cursors.Split)
      _ = _let_tmp_rhs36
      var _743_cst Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs36.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
      _ = _743_cst
      var _744_cs_k Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs36.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
      _ = _744_cs_k
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(Std_JSON_Grammar.Companion_Value_.Create_Bool_(_743_cst), _744_cs_k))
    }
  } else if ((_725_c) == (int16(_dafny.CodePoint('n')))) {
    var _745_valueOrError5 Std_Wrappers.Result = Std_JSON_ZeroCopy_Deserializer_Constants.Companion_Default___.Constant(cs, Std_JSON_Grammar.Companion_Default___.NULL())
    _ = _745_valueOrError5
    if ((_745_valueOrError5).IsFailure()) {
      return (_745_valueOrError5).PropagateFailure()
    } else {
      var _let_tmp_rhs37 Std_JSON_Utils_Cursors.Split = (_745_valueOrError5).Extract().(Std_JSON_Utils_Cursors.Split)
      _ = _let_tmp_rhs37
      var _746_cst Std_JSON_Utils_Views_Core.View__ = _let_tmp_rhs37.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Utils_Views_Core.View__)
      _ = _746_cst
      var _747_cs_k Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs37.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
      _ = _747_cs_k
      return Std_Wrappers.Companion_Result_.Create_Success_(Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(Std_JSON_Grammar.Companion_Value_.Create_Null_(_746_cst), _747_cs_k))
    }
  } else {
    var _748_valueOrError6 Std_Wrappers.Result = Std_JSON_ZeroCopy_Deserializer_Numbers.Companion_Default___.Number(cs)
    _ = _748_valueOrError6
    if ((_748_valueOrError6).IsFailure()) {
      return (_748_valueOrError6).PropagateFailure()
    } else {
      var _let_tmp_rhs38 Std_JSON_Utils_Cursors.Split = (_748_valueOrError6).Extract().(Std_JSON_Utils_Cursors.Split)
      _ = _let_tmp_rhs38
      var _749_num Std_JSON_Grammar.Jnumber = _let_tmp_rhs38.Get_().(Std_JSON_Utils_Cursors.Split_SP).T.(Std_JSON_Grammar.Jnumber)
      _ = _749_num
      var _750_cs_k Std_JSON_Utils_Cursors.Cursor__ = _let_tmp_rhs38.Get_().(Std_JSON_Utils_Cursors.Split_SP).Cs
      _ = _750_cs_k
      var _751_v Std_JSON_Grammar.Value = Std_JSON_Grammar.Companion_Value_.Create_Number_(_749_num)
      _ = _751_v
      var _752_sp Std_JSON_Utils_Cursors.Split = Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(_751_v, _750_cs_k)
      _ = _752_sp
      return Std_Wrappers.Companion_Result_.Create_Success_(_752_sp)
    }
  }
}
func (_static *CompanionStruct_Default___) ValueParser(cs Std_JSON_Utils_Cursors.Cursor__) func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  var _753_pre func (Std_JSON_Utils_Cursors.Cursor__) bool = (func (_754_cs Std_JSON_Utils_Cursors.Cursor__) func (Std_JSON_Utils_Cursors.Cursor__) bool {
    return func (_755_ps_k Std_JSON_Utils_Cursors.Cursor__) bool {
      return ((_755_ps_k).Length()) < ((_754_cs).Length())
    }
  })(cs)
  _ = _753_pre
  var _756_fn func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result = (func (_757_pre func (Std_JSON_Utils_Cursors.Cursor__) bool) func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
    return func (_758_ps_k Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
      return Companion_Default___.Value(_758_ps_k)
    }
  })(_753_pre)
  _ = _756_fn
  return _756_fn
}
// End of class Default__
