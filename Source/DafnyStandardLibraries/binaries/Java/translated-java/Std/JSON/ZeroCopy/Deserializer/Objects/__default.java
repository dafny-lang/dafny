// Class __default
// Dafny class __default compiled into Java
package Std.JSON.ZeroCopy.Deserializer.Objects;

import Std.Wrappers.*;
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
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Object(Std.JSON.Utils.Cursors.Cursor__ cs, java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>> json)
  {
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _687_valueOrError0 = __default.Bracketed(cs, json);
    if ((_687_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
      return (_687_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())));
    } else {
      Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>> _688_sp = (_687_valueOrError0).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
      return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), _688_sp);
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Open(Std.JSON.Utils.Cursors.Cursor__ cs) {
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Cursor__, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _689_valueOrError0 = (cs).<Std.JSON.Errors.DeserializationError>AssertByte(Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.OPEN());
    if ((_689_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
      return (_689_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>>PropagateFailure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()));
    } else {
      Std.JSON.Utils.Cursors.Cursor__ _690_cs = (_689_valueOrError0).Extract(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
      return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), (_690_cs).Split());
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Close(Std.JSON.Utils.Cursors.Cursor__ cs) {
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Cursor__, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _691_valueOrError0 = (cs).<Std.JSON.Errors.DeserializationError>AssertByte(Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.CLOSE());
    if ((_691_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
      return (_691_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>>PropagateFailure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()));
    } else {
      Std.JSON.Utils.Cursors.Cursor__ _692_cs = (_691_valueOrError0).Extract(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
      return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), (_692_cs).Split());
    }
  }
  public static Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>> BracketedFromParts(Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> open, Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> elems, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> close)
  {
    Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>> _693_sp = Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>create(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor()), Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>create(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor(), (open).dtor_t(), (elems).dtor_t(), (close).dtor_t()), (close).dtor_cs());
    return _693_sp;
  }
  public static Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> AppendWithSuffix(Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> elems, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jKeyValue> elem, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> sep)
  {
    Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__> _694_suffixed = Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>create(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), (elem).dtor_t(), Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>create_NonEmpty(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jcomma._typeDescriptor()), (sep).dtor_t()));
    Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> _695_elems_k = Std.JSON.Utils.Cursors.Split.<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>>create(dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor())), dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>concatenate((elems).dtor_t(), dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>> of(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor()), _694_suffixed)), (sep).dtor_cs());
    return _695_elems_k;
  }
  public static Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> AppendLast(Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> elems, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jKeyValue> elem, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> sep)
  {
    Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__> _696_suffixed = Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>create(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), (elem).dtor_t(), Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>create_Empty(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jcomma._typeDescriptor())));
    Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> _697_elems_k = Std.JSON.Utils.Cursors.Split.<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>>create(dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor())), dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>concatenate((elems).dtor_t(), dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>> of(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor()), _696_suffixed)), (elem).dtor_cs());
    return _697_elems_k;
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Elements(java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>> json, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> open, Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> elems)
  {
    TAIL_CALL_START: while (true) {
      Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jKeyValue>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _698_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.Element((elems).dtor_cs(), json);
      if ((_698_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jKeyValue>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
        return (_698_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jKeyValue>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())));
      } else {
        Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jKeyValue> _699_elem = (_698_valueOrError0).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jKeyValue>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
        if (((_699_elem).dtor_cs()).EOF_q()) {
          return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Failure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>create_EOF(Std.JSON.Errors.DeserializationError._typeDescriptor()));
        } else {
          Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> _700_sep = Std.JSON.ZeroCopy.Deserializer.Core.__default.TryStructural((_699_elem).dtor_cs());
          short _701_s0 = (((_700_sep).dtor_t()).dtor_t()).Peek();
          if (((_701_s0) == ((short) java.lang.Byte.toUnsignedInt(__default.SEPARATOR()))) && (((((_700_sep).dtor_t()).dtor_t()).Length()) == (1))) {
            Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> _702_sep = _700_sep;
            Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> _703_elems = __default.AppendWithSuffix(elems, _699_elem, _702_sep);
            java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>> _in96 = json;
            Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> _in97 = open;
            Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> _in98 = _703_elems;
            json = _in96;
            open = _in97;
            elems = _in98;
            continue TAIL_CALL_START;
          } else if (((_701_s0) == ((short) java.lang.Byte.toUnsignedInt(Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.CLOSE()))) && (((((_700_sep).dtor_t()).dtor_t()).Length()) == (1))) {
            Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> _704_sep = _700_sep;
            Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> _705_elems_k = __default.AppendLast(elems, _699_elem, _704_sep);
            Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>> _706_bracketed = __default.BracketedFromParts(open, _705_elems_k, _704_sep);
            return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), _706_bracketed);
          } else {
            byte _707_separator = __default.SEPARATOR();
            Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _708_pr = Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Failure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>create_ExpectingAnyByte(Std.JSON.Errors.DeserializationError._typeDescriptor(), dafny.DafnySequence.<java.lang.Byte> of(Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.CLOSE(), _707_separator), _701_s0));
            return _708_pr;
          }
        }
      }
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Bracketed(Std.JSON.Utils.Cursors.Cursor__ cs, java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>> json)
  {
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _709_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.Core.__default.<Std.JSON.Utils.Views.Core.View__>Structural(jopen._typeDescriptor(), cs, __default::Open);
    if ((_709_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
      return (_709_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())));
    } else {
      Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> _710_open = (_709_valueOrError0).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
      Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>> _711_elems = Std.JSON.Utils.Cursors.Split.<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>>create(dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor())), dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>> empty(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor())), (_710_open).dtor_cs());
      if ((((_710_open).dtor_cs()).Peek()) == ((short) java.lang.Byte.toUnsignedInt(Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.CLOSE()))) {
        java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>> _712_p = __default::Close;
        Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _713_valueOrError1 = Std.JSON.ZeroCopy.Deserializer.Core.__default.<Std.JSON.Utils.Views.Core.View__>Structural(jclose._typeDescriptor(), (_710_open).dtor_cs(), _712_p);
        if ((_713_valueOrError1).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
          return (_713_valueOrError1).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())));
        } else {
          Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> _714_close = (_713_valueOrError1).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
          return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), __default.BracketedFromParts(_710_open, _711_elems, _714_close));
        }
      } else {
        return __default.Elements(json, _710_open, _711_elems);
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
