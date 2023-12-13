// Class __default
// Dafny class __default compiled into Java
package Std.JSON.ZeroCopy.Deserializer.Objects;

import JavaInternal.*;
import Std.Wrappers.*;
import Std.FileIOInternalExterns.*;
import Std.BoundedInts.*;
import Std.Base64.*;
import Std.Math.*;
import Std.Collections.Seq.*;
import Std.Collections.Array.*;
import Std.Collections.Imap.*;
import Std.Collections.Map.*;
import Std.Collections.Set.*;
import Std.DynamicArray.*;
import Std.FileIO.*;
import Std.Arithmetic.MulInternals.*;
import Std.Arithmetic.ModInternals.*;
import Std.Arithmetic.DivInternals.*;
import Std.Arithmetic.DivMod.*;
import Std.Arithmetic.Power.*;
import Std.Arithmetic.Logarithm.*;
import Std.Arithmetic.Power2.*;
import Std.Strings.HexConversion.*;
import Std.Strings.DecimalConversion.*;
import Std.Strings.CharStrEscaping.*;
import Std.Strings.*;
import Std.Unicode.Base.*;
import Std.Unicode.Utf8EncodingForm.*;
import Std.Unicode.Utf16EncodingForm.*;
import Std.Unicode.UnicodeStringsWithUnicodeChar.*;
import Std.Unicode.Utf8EncodingScheme.*;
import Std.JSON.Values.*;
import Std.JSON.Errors.*;
import Std.JSON.Spec.*;
import Std.JSON.Utils.Views.Core.*;
import Std.JSON.Utils.Views.Writers.*;
import Std.JSON.Utils.Lexers.Core.*;
import Std.JSON.Utils.Lexers.Strings.*;
import Std.JSON.Utils.Cursors.*;
import Std.JSON.Utils.Parsers.*;
import Std.JSON.Grammar.*;
import Std.JSON.ByteStrConversion.*;
import Std.JSON.Serializer.*;
import Std.JSON.Deserializer.Uint16StrConversion.*;
import Std.JSON.Deserializer.*;
import Std.JSON.ConcreteSyntax.Spec.*;
import Std.JSON.ZeroCopy.Serializer.*;
import Std.JSON.ZeroCopy.Deserializer.Core.*;
import Std.JSON.ZeroCopy.Deserializer.Strings.*;
import Std.JSON.ZeroCopy.Deserializer.Numbers.*;
import Std.JSON.ZeroCopy.Deserializer.ObjectParams.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Object(Std.JSON.Utils.Cursors.Cursor__ cs, Std.JSON.Utils.Parsers.SubParser__<Std.JSON.Grammar.Value, Std.JSON.Errors.DeserializationError> json)
  {
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _696_valueOrError0 = __default.Bracketed(cs, json);
    if ((_696_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
      return (_696_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())));
    } else {
      Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>> _697_sp = (_696_valueOrError0).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
      return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), _697_sp);
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Open(Std.JSON.Utils.Cursors.Cursor__ cs) {
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Cursor__, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _698_valueOrError0 = (cs).<Std.JSON.Errors.DeserializationError>AssertByte(Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.OPEN());
    if ((_698_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
      return (_698_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>>PropagateFailure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()));
    } else {
      Std.JSON.Utils.Cursors.Cursor__ _699_cs = (_698_valueOrError0).Extract(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
      return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), (_699_cs).Split());
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Close(Std.JSON.Utils.Cursors.Cursor__ cs) {
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Cursor__, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _700_valueOrError0 = (cs).<Std.JSON.Errors.DeserializationError>AssertByte(Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.CLOSE());
    if ((_700_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
      return (_700_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>>PropagateFailure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()));
    } else {
      Std.JSON.Utils.Cursors.Cursor__ _701_cs = (_700_valueOrError0).Extract(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
      return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), (_701_cs).Split());
    }
  }
  public static Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>> BracketedFromParts(Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> open, Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> elems, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> close)
  {
    Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>> _702_sp = Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>create(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor()), Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>create(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor(), (open).dtor_t(), (elems).dtor_t(), (close).dtor_t()), (close).dtor_cs());
    return _702_sp;
  }
  public static Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> AppendWithSuffix(Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> elems, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jKeyValue> elem, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> sep)
  {
    Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__> _703_suffixed = Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>create(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), (elem).dtor_t(), Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>create_NonEmpty(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jcomma._typeDescriptor()), (sep).dtor_t()));
    Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> _704_elems_k = Std.JSON.Utils.Cursors.Split.<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>>create(dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor())), dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>concatenate((elems).dtor_t(), dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>> of(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor()), _703_suffixed)), (sep).dtor_cs());
    return _704_elems_k;
  }
  public static Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> AppendLast(Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> elems, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jKeyValue> elem, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> sep)
  {
    Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__> _705_suffixed = Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>create(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), (elem).dtor_t(), Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>create_Empty(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jcomma._typeDescriptor())));
    Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> _706_elems_k = Std.JSON.Utils.Cursors.Split.<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>>create(dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor())), dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>concatenate((elems).dtor_t(), dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>> of(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor()), _705_suffixed)), (elem).dtor_cs());
    return _706_elems_k;
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Elements(Std.JSON.Utils.Parsers.SubParser__<Std.JSON.Grammar.Value, Std.JSON.Errors.DeserializationError> json, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> open, Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> elems)
  {
    TAIL_CALL_START: while (true) {
      Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jKeyValue>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _707_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.Element((elems).dtor_cs(), json);
      if ((_707_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jKeyValue>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
        return (_707_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jKeyValue>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())));
      } else {
        Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jKeyValue> _708_elem = (_707_valueOrError0).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jKeyValue>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
        if (((_708_elem).dtor_cs()).EOF_q()) {
          return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Failure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>create_EOF(Std.JSON.Errors.DeserializationError._typeDescriptor()));
        } else {
          Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> _709_sep = Std.JSON.ZeroCopy.Deserializer.Core.__default.TryStructural((_708_elem).dtor_cs());
          short _710_s0 = (((_709_sep).dtor_t()).dtor_t()).Peek();
          if (((_710_s0) == ((short) java.lang.Byte.toUnsignedInt(__default.SEPARATOR()))) && (((((_709_sep).dtor_t()).dtor_t()).Length()) == (1))) {
            Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> _711_sep = _709_sep;
            Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> _712_elems = __default.AppendWithSuffix(elems, _708_elem, _711_sep);
            Std.JSON.Utils.Parsers.SubParser__<Std.JSON.Grammar.Value, Std.JSON.Errors.DeserializationError> _in97 = json;
            Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> _in98 = open;
            Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> _in99 = _712_elems;
            json = _in97;
            open = _in98;
            elems = _in99;
            continue TAIL_CALL_START;
          } else if (((_710_s0) == ((short) java.lang.Byte.toUnsignedInt(Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.CLOSE()))) && (((((_709_sep).dtor_t()).dtor_t()).Length()) == (1))) {
            Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> _713_sep = _709_sep;
            Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> _714_elems_k = __default.AppendLast(elems, _708_elem, _713_sep);
            Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>> _715_bracketed = __default.BracketedFromParts(open, _714_elems_k, _713_sep);
            return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), _715_bracketed);
          } else {
            byte _716_separator = __default.SEPARATOR();
            Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _717_pr = Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Failure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>create_ExpectingAnyByte(Std.JSON.Errors.DeserializationError._typeDescriptor(), dafny.DafnySequence.<java.lang.Byte> of(Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.CLOSE(), _716_separator), _710_s0));
            return _717_pr;
          }
        }
      }
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Bracketed(Std.JSON.Utils.Cursors.Cursor__ cs, Std.JSON.Utils.Parsers.SubParser__<Std.JSON.Grammar.Value, Std.JSON.Errors.DeserializationError> json)
  {
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _718_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.Core.__default.<Std.JSON.Utils.Views.Core.View__>Structural(jopen._typeDescriptor(), cs, Std.JSON.Utils.Parsers.Parser__.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Errors.DeserializationError>create(jopen._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), __default::Open));
    if ((_718_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
      return (_718_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())));
    } else {
      Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> _719_open = (_718_valueOrError0).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
      Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> _720_elems = Std.JSON.Utils.Cursors.Split.<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>>create(dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor())), dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>> empty(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor())), (_719_open).dtor_cs());
      if ((((_719_open).dtor_cs()).Peek()) == ((short) java.lang.Byte.toUnsignedInt(Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.CLOSE()))) {
        Std.JSON.Utils.Parsers.Parser__<Std.JSON.Utils.Views.Core.View__, Std.JSON.Errors.DeserializationError> _721_p = Std.JSON.Utils.Parsers.Parser__.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Errors.DeserializationError>create(jclose._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), __default::Close);
        Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _722_valueOrError1 = Std.JSON.ZeroCopy.Deserializer.Core.__default.<Std.JSON.Utils.Views.Core.View__>Structural(jclose._typeDescriptor(), (_719_open).dtor_cs(), _721_p);
        if ((_722_valueOrError1).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
          return (_722_valueOrError1).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())));
        } else {
          Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> _723_close = (_722_valueOrError1).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
          return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), __default.BracketedFromParts(_719_open, _720_elems, _723_close));
        }
      } else {
        return __default.Elements(json, _719_open, _720_elems);
      }
    }
  }
  public static java.util.function.Function<Std.JSON.Utils.Views.Core.View__, dafny.DafnySequence<? extends java.lang.Byte>> SpecViewOpen()
  {
    return Std.JSON.ZeroCopy.Deserializer.Core.__default.SpecView();
  }
  public static java.util.function.Function<Std.JSON.Utils.Views.Core.View__, dafny.DafnySequence<? extends java.lang.Byte>> SpecViewClose()
  {
    return Std.JSON.ZeroCopy.Deserializer.Core.__default.SpecView();
  }
  public static byte SEPARATOR()
  {
    return ((byte) (','));
  }
  @Override
  public java.lang.String toString() {
    return "Std.JSON.ZeroCopy.Deserializer.Objects._default";
  }
}
