// Package Std_JSON_ZeroCopy_Deserializer_Arrays
// Dafny module Std_JSON_ZeroCopy_Deserializer_Arrays compiled into Go

package Std_JSON_ZeroCopy_Deserializer_Arrays

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
  return "Std_JSON_ZeroCopy_Deserializer_Arrays.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) Array(cs Std_JSON_Utils_Cursors.Cursor__, json func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result) Std_Wrappers.Result {
  var _695_valueOrError0 Std_Wrappers.Result = Companion_Default___.Bracketed(cs, json)
  _ = _695_valueOrError0
  if ((_695_valueOrError0).IsFailure()) {
    return (_695_valueOrError0).PropagateFailure()
  } else {
    var _696_sp Std_JSON_Utils_Cursors.Split = (_695_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Split)
    _ = _696_sp
    return Std_Wrappers.Companion_Result_.Create_Success_(_696_sp)
  }
}
func (_static *CompanionStruct_Default___) Open(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  var _697_valueOrError0 Std_Wrappers.Result = (cs).AssertByte(Std_JSON_ZeroCopy_Deserializer_ArrayParams.Companion_Default___.OPEN())
  _ = _697_valueOrError0
  if ((_697_valueOrError0).IsFailure()) {
    return (_697_valueOrError0).PropagateFailure()
  } else {
    var _698_cs Std_JSON_Utils_Cursors.Cursor__ = (_697_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Cursor__)
    _ = _698_cs
    return Std_Wrappers.Companion_Result_.Create_Success_((_698_cs).Split())
  }
}
func (_static *CompanionStruct_Default___) Close(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  var _699_valueOrError0 Std_Wrappers.Result = (cs).AssertByte(Std_JSON_ZeroCopy_Deserializer_ArrayParams.Companion_Default___.CLOSE())
  _ = _699_valueOrError0
  if ((_699_valueOrError0).IsFailure()) {
    return (_699_valueOrError0).PropagateFailure()
  } else {
    var _700_cs Std_JSON_Utils_Cursors.Cursor__ = (_699_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Cursor__)
    _ = _700_cs
    return Std_Wrappers.Companion_Result_.Create_Success_((_700_cs).Split())
  }
}
func (_static *CompanionStruct_Default___) BracketedFromParts(open Std_JSON_Utils_Cursors.Split, elems Std_JSON_Utils_Cursors.Split, close_ Std_JSON_Utils_Cursors.Split) Std_JSON_Utils_Cursors.Split {
  var _701_sp Std_JSON_Utils_Cursors.Split = Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(Std_JSON_Grammar.Companion_Bracketed_.Create_Bracketed_((open).Dtor_t().(Std_JSON_Grammar.Structural), (elems).Dtor_t().(_dafny.Sequence), (close_).Dtor_t().(Std_JSON_Grammar.Structural)), (close_).Dtor_cs())
  _ = _701_sp
  return _701_sp
}
func (_static *CompanionStruct_Default___) AppendWithSuffix(elems Std_JSON_Utils_Cursors.Split, elem Std_JSON_Utils_Cursors.Split, sep Std_JSON_Utils_Cursors.Split) Std_JSON_Utils_Cursors.Split {
  var _702_suffixed Std_JSON_Grammar.Suffixed = Std_JSON_Grammar.Companion_Suffixed_.Create_Suffixed_((elem).Dtor_t().(Std_JSON_Grammar.Value), Std_JSON_Grammar.Companion_Maybe_.Create_NonEmpty_((sep).Dtor_t().(Std_JSON_Grammar.Structural)))
  _ = _702_suffixed
  var _703_elems_k Std_JSON_Utils_Cursors.Split = Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(_dafny.Companion_Sequence_.Concatenate((elems).Dtor_t().(_dafny.Sequence), _dafny.SeqOf(_702_suffixed)), (sep).Dtor_cs())
  _ = _703_elems_k
  return _703_elems_k
}
func (_static *CompanionStruct_Default___) AppendLast(elems Std_JSON_Utils_Cursors.Split, elem Std_JSON_Utils_Cursors.Split, sep Std_JSON_Utils_Cursors.Split) Std_JSON_Utils_Cursors.Split {
  var _704_suffixed Std_JSON_Grammar.Suffixed = Std_JSON_Grammar.Companion_Suffixed_.Create_Suffixed_((elem).Dtor_t().(Std_JSON_Grammar.Value), Std_JSON_Grammar.Companion_Maybe_.Create_Empty_())
  _ = _704_suffixed
  var _705_elems_k Std_JSON_Utils_Cursors.Split = Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(_dafny.Companion_Sequence_.Concatenate((elems).Dtor_t().(_dafny.Sequence), _dafny.SeqOf(_704_suffixed)), (elem).Dtor_cs())
  _ = _705_elems_k
  return _705_elems_k
}
func (_static *CompanionStruct_Default___) Elements(json func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result, open Std_JSON_Utils_Cursors.Split, elems Std_JSON_Utils_Cursors.Split) Std_Wrappers.Result {
  goto TAIL_CALL_START
  TAIL_CALL_START:
  var _706_valueOrError0 Std_Wrappers.Result = Std_JSON_ZeroCopy_Deserializer_ArrayParams.Companion_Default___.Element((elems).Dtor_cs(), json)
  _ = _706_valueOrError0
  if ((_706_valueOrError0).IsFailure()) {
    return (_706_valueOrError0).PropagateFailure()
  } else {
    var _707_elem Std_JSON_Utils_Cursors.Split = (_706_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Split)
    _ = _707_elem
    if (((_707_elem).Dtor_cs()).EOF_q()) {
      return Std_Wrappers.Companion_Result_.Create_Failure_(Std_JSON_Utils_Cursors.Companion_CursorError_.Create_EOF_())
    } else {
      var _708_sep Std_JSON_Utils_Cursors.Split = Std_JSON_ZeroCopy_Deserializer_Core.Companion_Default___.TryStructural((_707_elem).Dtor_cs())
      _ = _708_sep
      var _709_s0 int16 = (((_708_sep).Dtor_t().(Std_JSON_Grammar.Structural)).Dtor_t().(Std_JSON_Utils_Views_Core.View__)).Peek()
      _ = _709_s0
      if (((_709_s0) == (int16(Companion_Default___.SEPARATOR()))) && (((((_708_sep).Dtor_t().(Std_JSON_Grammar.Structural)).Dtor_t().(Std_JSON_Utils_Views_Core.View__)).Length()) == (uint32(1)))) {
        var _710_sep Std_JSON_Utils_Cursors.Split = _708_sep
        _ = _710_sep
        var _711_elems Std_JSON_Utils_Cursors.Split = Companion_Default___.AppendWithSuffix(elems, _707_elem, _710_sep)
        _ = _711_elems
        var _in99 func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result = json
        _ = _in99
        var _in100 Std_JSON_Utils_Cursors.Split = open
        _ = _in100
        var _in101 Std_JSON_Utils_Cursors.Split = _711_elems
        _ = _in101
        json = _in99
        open = _in100
        elems = _in101
        goto TAIL_CALL_START
      } else if (((_709_s0) == (int16(Std_JSON_ZeroCopy_Deserializer_ArrayParams.Companion_Default___.CLOSE()))) && (((((_708_sep).Dtor_t().(Std_JSON_Grammar.Structural)).Dtor_t().(Std_JSON_Utils_Views_Core.View__)).Length()) == (uint32(1)))) {
        var _712_sep Std_JSON_Utils_Cursors.Split = _708_sep
        _ = _712_sep
        var _713_elems_k Std_JSON_Utils_Cursors.Split = Companion_Default___.AppendLast(elems, _707_elem, _712_sep)
        _ = _713_elems_k
        var _714_bracketed Std_JSON_Utils_Cursors.Split = Companion_Default___.BracketedFromParts(open, _713_elems_k, _712_sep)
        _ = _714_bracketed
        return Std_Wrappers.Companion_Result_.Create_Success_(_714_bracketed)
      } else {
        var _715_separator uint8 = Companion_Default___.SEPARATOR()
        _ = _715_separator
        var _716_pr Std_Wrappers.Result = Std_Wrappers.Companion_Result_.Create_Failure_(Std_JSON_Utils_Cursors.Companion_CursorError_.Create_ExpectingAnyByte_(_dafny.SeqOf(Std_JSON_ZeroCopy_Deserializer_ArrayParams.Companion_Default___.CLOSE(), _715_separator), _709_s0))
        _ = _716_pr
        return _716_pr
      }
    }
  }
}
func (_static *CompanionStruct_Default___) Bracketed(cs Std_JSON_Utils_Cursors.Cursor__, json func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result) Std_Wrappers.Result {
  var _717_valueOrError0 Std_Wrappers.Result = Std_JSON_ZeroCopy_Deserializer_Core.Companion_Default___.Structural(cs, func (coer45 func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result) func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
    return func (arg47 Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
      return coer45(arg47)
    }
  }(Companion_Default___.Open))
  _ = _717_valueOrError0
  if ((_717_valueOrError0).IsFailure()) {
    return (_717_valueOrError0).PropagateFailure()
  } else {
    var _718_open Std_JSON_Utils_Cursors.Split = (_717_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Split)
    _ = _718_open
    var _719_elems Std_JSON_Utils_Cursors.Split = Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(_dafny.SeqOf(), (_718_open).Dtor_cs())
    _ = _719_elems
    if ((((_718_open).Dtor_cs()).Peek()) == (int16(Std_JSON_ZeroCopy_Deserializer_ArrayParams.Companion_Default___.CLOSE()))) {
      var _720_p func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result = Companion_Default___.Close
      _ = _720_p
      var _721_valueOrError1 Std_Wrappers.Result = Std_JSON_ZeroCopy_Deserializer_Core.Companion_Default___.Structural((_718_open).Dtor_cs(), func (coer46 func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result) func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
        return func (arg48 Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
          return coer46(arg48)
        }
      }(_720_p))
      _ = _721_valueOrError1
      if ((_721_valueOrError1).IsFailure()) {
        return (_721_valueOrError1).PropagateFailure()
      } else {
        var _722_close Std_JSON_Utils_Cursors.Split = (_721_valueOrError1).Extract().(Std_JSON_Utils_Cursors.Split)
        _ = _722_close
        return Std_Wrappers.Companion_Result_.Create_Success_(Companion_Default___.BracketedFromParts(_718_open, _719_elems, _722_close))
      }
    } else {
      return Companion_Default___.Elements(json, _718_open, _719_elems)
    }
  }
}
func (_static *CompanionStruct_Default___) SpecViewOpen() func (Std_JSON_Utils_Views_Core.View__) _dafny.Sequence {
  return Std_JSON_ZeroCopy_Deserializer_Core.Companion_Default___.SpecView()
}
func (_static *CompanionStruct_Default___) SpecViewClose() func (Std_JSON_Utils_Views_Core.View__) _dafny.Sequence {
  return Std_JSON_ZeroCopy_Deserializer_Core.Companion_Default___.SpecView()
}
func (_static *CompanionStruct_Default___) SEPARATOR() uint8 {
  return uint8(_dafny.CodePoint(','))
}
// End of class Default__

// Definition of class Jopen
type Jopen struct {
}

func New_Jopen_() *Jopen {
  _this := Jopen{}

  return &_this
}

type CompanionStruct_Jopen_ struct {
}
var Companion_Jopen_ = CompanionStruct_Jopen_ {
}

func (*Jopen) String() string {
  return "Std_JSON_ZeroCopy_Deserializer_Arrays.Jopen"
}
func (_this *CompanionStruct_Jopen_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf(Std_JSON_ZeroCopy_Deserializer_ArrayParams.Companion_Default___.OPEN()))
}
// End of class Jopen

func Type_Jopen_() _dafny.TypeDescriptor {
  return type_Jopen_{}
}

type type_Jopen_ struct {
}

func (_this type_Jopen_) Default() interface{} {
  return Companion_Jopen_.Witness()
}

func (_this type_Jopen_) String() string {
  return "Std_JSON_ZeroCopy_Deserializer_Arrays.Jopen"
}

// Definition of class Jclose
type Jclose struct {
}

func New_Jclose_() *Jclose {
  _this := Jclose{}

  return &_this
}

type CompanionStruct_Jclose_ struct {
}
var Companion_Jclose_ = CompanionStruct_Jclose_ {
}

func (*Jclose) String() string {
  return "Std_JSON_ZeroCopy_Deserializer_Arrays.Jclose"
}
func (_this *CompanionStruct_Jclose_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf(Std_JSON_ZeroCopy_Deserializer_ArrayParams.Companion_Default___.CLOSE()))
}
// End of class Jclose

func Type_Jclose_() _dafny.TypeDescriptor {
  return type_Jclose_{}
}

type type_Jclose_ struct {
}

func (_this type_Jclose_) Default() interface{} {
  return Companion_Jclose_.Witness()
}

func (_this type_Jclose_) String() string {
  return "Std_JSON_ZeroCopy_Deserializer_Arrays.Jclose"
}
