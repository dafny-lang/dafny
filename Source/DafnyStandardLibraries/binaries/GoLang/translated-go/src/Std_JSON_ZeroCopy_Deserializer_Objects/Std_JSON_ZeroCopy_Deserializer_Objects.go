// Package Std_JSON_ZeroCopy_Deserializer_Objects
// Dafny module Std_JSON_ZeroCopy_Deserializer_Objects compiled into Go

package Std_JSON_ZeroCopy_Deserializer_Objects

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
  return "Std_JSON_ZeroCopy_Deserializer_Objects.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) Object(cs Std_JSON_Utils_Cursors.Cursor__, json func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result) Std_Wrappers.Result {
  var _667_valueOrError0 Std_Wrappers.Result = Companion_Default___.Bracketed(cs, json)
  _ = _667_valueOrError0
  if ((_667_valueOrError0).IsFailure()) {
    return (_667_valueOrError0).PropagateFailure()
  } else {
    var _668_sp Std_JSON_Utils_Cursors.Split = (_667_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Split)
    _ = _668_sp
    return Std_Wrappers.Companion_Result_.Create_Success_(_668_sp)
  }
}
func (_static *CompanionStruct_Default___) Open(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  var _669_valueOrError0 Std_Wrappers.Result = (cs).AssertByte(Std_JSON_ZeroCopy_Deserializer_ObjectParams.Companion_Default___.OPEN())
  _ = _669_valueOrError0
  if ((_669_valueOrError0).IsFailure()) {
    return (_669_valueOrError0).PropagateFailure()
  } else {
    var _670_cs Std_JSON_Utils_Cursors.Cursor__ = (_669_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Cursor__)
    _ = _670_cs
    return Std_Wrappers.Companion_Result_.Create_Success_((_670_cs).Split())
  }
}
func (_static *CompanionStruct_Default___) Close(cs Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
  var _671_valueOrError0 Std_Wrappers.Result = (cs).AssertByte(Std_JSON_ZeroCopy_Deserializer_ObjectParams.Companion_Default___.CLOSE())
  _ = _671_valueOrError0
  if ((_671_valueOrError0).IsFailure()) {
    return (_671_valueOrError0).PropagateFailure()
  } else {
    var _672_cs Std_JSON_Utils_Cursors.Cursor__ = (_671_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Cursor__)
    _ = _672_cs
    return Std_Wrappers.Companion_Result_.Create_Success_((_672_cs).Split())
  }
}
func (_static *CompanionStruct_Default___) BracketedFromParts(open Std_JSON_Utils_Cursors.Split, elems Std_JSON_Utils_Cursors.Split, close_ Std_JSON_Utils_Cursors.Split) Std_JSON_Utils_Cursors.Split {
  var _673_sp Std_JSON_Utils_Cursors.Split = Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(Std_JSON_Grammar.Companion_Bracketed_.Create_Bracketed_((open).Dtor_t().(Std_JSON_Grammar.Structural), (elems).Dtor_t().(_dafny.Sequence), (close_).Dtor_t().(Std_JSON_Grammar.Structural)), (close_).Dtor_cs())
  _ = _673_sp
  return _673_sp
}
func (_static *CompanionStruct_Default___) AppendWithSuffix(elems Std_JSON_Utils_Cursors.Split, elem Std_JSON_Utils_Cursors.Split, sep Std_JSON_Utils_Cursors.Split) Std_JSON_Utils_Cursors.Split {
  var _674_suffixed Std_JSON_Grammar.Suffixed = Std_JSON_Grammar.Companion_Suffixed_.Create_Suffixed_((elem).Dtor_t().(Std_JSON_Grammar.JKeyValue), Std_JSON_Grammar.Companion_Maybe_.Create_NonEmpty_((sep).Dtor_t().(Std_JSON_Grammar.Structural)))
  _ = _674_suffixed
  var _675_elems_k Std_JSON_Utils_Cursors.Split = Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(_dafny.Companion_Sequence_.Concatenate((elems).Dtor_t().(_dafny.Sequence), _dafny.SeqOf(_674_suffixed)), (sep).Dtor_cs())
  _ = _675_elems_k
  return _675_elems_k
}
func (_static *CompanionStruct_Default___) AppendLast(elems Std_JSON_Utils_Cursors.Split, elem Std_JSON_Utils_Cursors.Split, sep Std_JSON_Utils_Cursors.Split) Std_JSON_Utils_Cursors.Split {
  var _676_suffixed Std_JSON_Grammar.Suffixed = Std_JSON_Grammar.Companion_Suffixed_.Create_Suffixed_((elem).Dtor_t().(Std_JSON_Grammar.JKeyValue), Std_JSON_Grammar.Companion_Maybe_.Create_Empty_())
  _ = _676_suffixed
  var _677_elems_k Std_JSON_Utils_Cursors.Split = Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(_dafny.Companion_Sequence_.Concatenate((elems).Dtor_t().(_dafny.Sequence), _dafny.SeqOf(_676_suffixed)), (elem).Dtor_cs())
  _ = _677_elems_k
  return _677_elems_k
}
func (_static *CompanionStruct_Default___) Elements(json func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result, open Std_JSON_Utils_Cursors.Split, elems Std_JSON_Utils_Cursors.Split) Std_Wrappers.Result {
  goto TAIL_CALL_START
  TAIL_CALL_START:
  var _678_valueOrError0 Std_Wrappers.Result = Std_JSON_ZeroCopy_Deserializer_ObjectParams.Companion_Default___.Element((elems).Dtor_cs(), json)
  _ = _678_valueOrError0
  if ((_678_valueOrError0).IsFailure()) {
    return (_678_valueOrError0).PropagateFailure()
  } else {
    var _679_elem Std_JSON_Utils_Cursors.Split = (_678_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Split)
    _ = _679_elem
    if (((_679_elem).Dtor_cs()).EOF_q()) {
      return Std_Wrappers.Companion_Result_.Create_Failure_(Std_JSON_Utils_Cursors.Companion_CursorError_.Create_EOF_())
    } else {
      var _680_sep Std_JSON_Utils_Cursors.Split = Std_JSON_ZeroCopy_Deserializer_Core.Companion_Default___.TryStructural((_679_elem).Dtor_cs())
      _ = _680_sep
      var _681_s0 int16 = (((_680_sep).Dtor_t().(Std_JSON_Grammar.Structural)).Dtor_t().(Std_JSON_Utils_Views_Core.View__)).Peek()
      _ = _681_s0
      if (((_681_s0) == (int16(Companion_Default___.SEPARATOR()))) && (((((_680_sep).Dtor_t().(Std_JSON_Grammar.Structural)).Dtor_t().(Std_JSON_Utils_Views_Core.View__)).Length()) == (uint32(1)))) {
        var _682_sep Std_JSON_Utils_Cursors.Split = _680_sep
        _ = _682_sep
        var _683_elems Std_JSON_Utils_Cursors.Split = Companion_Default___.AppendWithSuffix(elems, _679_elem, _682_sep)
        _ = _683_elems
        var _in96 func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result = json
        _ = _in96
        var _in97 Std_JSON_Utils_Cursors.Split = open
        _ = _in97
        var _in98 Std_JSON_Utils_Cursors.Split = _683_elems
        _ = _in98
        json = _in96
        open = _in97
        elems = _in98
        goto TAIL_CALL_START
      } else if (((_681_s0) == (int16(Std_JSON_ZeroCopy_Deserializer_ObjectParams.Companion_Default___.CLOSE()))) && (((((_680_sep).Dtor_t().(Std_JSON_Grammar.Structural)).Dtor_t().(Std_JSON_Utils_Views_Core.View__)).Length()) == (uint32(1)))) {
        var _684_sep Std_JSON_Utils_Cursors.Split = _680_sep
        _ = _684_sep
        var _685_elems_k Std_JSON_Utils_Cursors.Split = Companion_Default___.AppendLast(elems, _679_elem, _684_sep)
        _ = _685_elems_k
        var _686_bracketed Std_JSON_Utils_Cursors.Split = Companion_Default___.BracketedFromParts(open, _685_elems_k, _684_sep)
        _ = _686_bracketed
        return Std_Wrappers.Companion_Result_.Create_Success_(_686_bracketed)
      } else {
        var _687_separator uint8 = Companion_Default___.SEPARATOR()
        _ = _687_separator
        var _688_pr Std_Wrappers.Result = Std_Wrappers.Companion_Result_.Create_Failure_(Std_JSON_Utils_Cursors.Companion_CursorError_.Create_ExpectingAnyByte_(_dafny.SeqOf(Std_JSON_ZeroCopy_Deserializer_ObjectParams.Companion_Default___.CLOSE(), _687_separator), _681_s0))
        _ = _688_pr
        return _688_pr
      }
    }
  }
}
func (_static *CompanionStruct_Default___) Bracketed(cs Std_JSON_Utils_Cursors.Cursor__, json func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result) Std_Wrappers.Result {
  var _689_valueOrError0 Std_Wrappers.Result = Std_JSON_ZeroCopy_Deserializer_Core.Companion_Default___.Structural(cs, func (coer43 func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result) func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
    return func (arg45 Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
      return coer43(arg45)
    }
  }(Companion_Default___.Open))
  _ = _689_valueOrError0
  if ((_689_valueOrError0).IsFailure()) {
    return (_689_valueOrError0).PropagateFailure()
  } else {
    var _690_open Std_JSON_Utils_Cursors.Split = (_689_valueOrError0).Extract().(Std_JSON_Utils_Cursors.Split)
    _ = _690_open
    var _691_elems Std_JSON_Utils_Cursors.Split = Std_JSON_Utils_Cursors.Companion_Split_.Create_SP_(_dafny.SeqOf(), (_690_open).Dtor_cs())
    _ = _691_elems
    if ((((_690_open).Dtor_cs()).Peek()) == (int16(Std_JSON_ZeroCopy_Deserializer_ObjectParams.Companion_Default___.CLOSE()))) {
      var _692_p func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result = Companion_Default___.Close
      _ = _692_p
      var _693_valueOrError1 Std_Wrappers.Result = Std_JSON_ZeroCopy_Deserializer_Core.Companion_Default___.Structural((_690_open).Dtor_cs(), func (coer44 func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result) func (Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
        return func (arg46 Std_JSON_Utils_Cursors.Cursor__) Std_Wrappers.Result {
          return coer44(arg46)
        }
      }(_692_p))
      _ = _693_valueOrError1
      if ((_693_valueOrError1).IsFailure()) {
        return (_693_valueOrError1).PropagateFailure()
      } else {
        var _694_close Std_JSON_Utils_Cursors.Split = (_693_valueOrError1).Extract().(Std_JSON_Utils_Cursors.Split)
        _ = _694_close
        return Std_Wrappers.Companion_Result_.Create_Success_(Companion_Default___.BracketedFromParts(_690_open, _691_elems, _694_close))
      }
    } else {
      return Companion_Default___.Elements(json, _690_open, _691_elems)
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
  return "Std_JSON_ZeroCopy_Deserializer_Objects.Jopen"
}
func (_this *CompanionStruct_Jopen_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf(Std_JSON_ZeroCopy_Deserializer_ObjectParams.Companion_Default___.OPEN()))
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
  return "Std_JSON_ZeroCopy_Deserializer_Objects.Jopen"
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
  return "Std_JSON_ZeroCopy_Deserializer_Objects.Jclose"
}
func (_this *CompanionStruct_Jclose_) Witness() Std_JSON_Utils_Views_Core.View__ {
  return Std_JSON_Utils_Views_Core.Companion_View___.OfBytes(_dafny.SeqOf(Std_JSON_ZeroCopy_Deserializer_ObjectParams.Companion_Default___.CLOSE()))
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
  return "Std_JSON_ZeroCopy_Deserializer_Objects.Jclose"
}
