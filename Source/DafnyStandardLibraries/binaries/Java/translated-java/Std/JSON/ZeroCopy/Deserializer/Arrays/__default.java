// Class __default
// Dafny class __default compiled into Java
package Std.JSON.ZeroCopy.Deserializer.Arrays;

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
import Std.JSON.ZeroCopy.Deserializer.Objects.*;
import Std.JSON.ZeroCopy.Deserializer.ArrayParams.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Array(Std.JSON.Utils.Cursors.Cursor__ cs, java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>> json)
  {
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _715_valueOrError0 = __default.Bracketed(cs, json);
    if ((_715_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
      return (_715_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())));
    } else {
      Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>> _716_sp = (_715_valueOrError0).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
      return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), _716_sp);
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Open(Std.JSON.Utils.Cursors.Cursor__ cs) {
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Cursor__, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _717_valueOrError0 = (cs).<Std.JSON.Errors.DeserializationError>AssertByte(Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.ZeroCopy.Deserializer.ArrayParams.__default.OPEN());
    if ((_717_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
      return (_717_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>>PropagateFailure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()));
    } else {
      Std.JSON.Utils.Cursors.Cursor__ _718_cs = (_717_valueOrError0).Extract(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
      return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), (_718_cs).Split());
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Close(Std.JSON.Utils.Cursors.Cursor__ cs) {
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Cursor__, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _719_valueOrError0 = (cs).<Std.JSON.Errors.DeserializationError>AssertByte(Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.ZeroCopy.Deserializer.ArrayParams.__default.CLOSE());
    if ((_719_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
      return (_719_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>>PropagateFailure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()));
    } else {
      Std.JSON.Utils.Cursors.Cursor__ _720_cs = (_719_valueOrError0).Extract(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
      return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), (_720_cs).Split());
    }
  }
  public static Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>> BracketedFromParts(Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> open, Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>>> elems, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> close)
  {
    Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>> _721_sp = Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>create(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor()), Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>create(jopen._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor(), (open).dtor_t(), (elems).dtor_t(), (close).dtor_t()), (close).dtor_cs());
    return _721_sp;
  }
  public static Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>>> AppendWithSuffix(Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>>> elems, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value> elem, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> sep)
  {
    Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__> _722_suffixed = Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>create(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), (elem).dtor_t(), Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>create_NonEmpty(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jcomma._typeDescriptor()), (sep).dtor_t()));
    Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>>> _723_elems_k = Std.JSON.Utils.Cursors.Split.<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>>>create(dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor())), dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>>concatenate((elems).dtor_t(), dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>> of(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor()), _722_suffixed)), (sep).dtor_cs());
    return _723_elems_k;
  }
  public static Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>>> AppendLast(Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>>> elems, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value> elem, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> sep)
  {
    Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__> _724_suffixed = Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>create(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), (elem).dtor_t(), Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>create_Empty(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jcomma._typeDescriptor())));
    Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>>> _725_elems_k = Std.JSON.Utils.Cursors.Split.<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>>>create(dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor())), dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>>concatenate((elems).dtor_t(), dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>> of(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor()), _724_suffixed)), (elem).dtor_cs());
    return _725_elems_k;
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Elements(java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>> json, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> open, Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>>> elems)
  {
    TAIL_CALL_START: while (true) {
      Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _726_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.ArrayParams.__default.Element((elems).dtor_cs(), json);
      if ((_726_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
        return (_726_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())));
      } else {
        Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value> _727_elem = (_726_valueOrError0).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
        if (((_727_elem).dtor_cs()).EOF_q()) {
          return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Failure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>create_EOF(Std.JSON.Errors.DeserializationError._typeDescriptor()));
        } else {
          Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> _728_sep = Std.JSON.ZeroCopy.Deserializer.Core.__default.TryStructural((_727_elem).dtor_cs());
          short _729_s0 = (((_728_sep).dtor_t()).dtor_t()).Peek();
          if (((_729_s0) == ((short) java.lang.Byte.toUnsignedInt(__default.SEPARATOR()))) && (((((_728_sep).dtor_t()).dtor_t()).Length()) == (1))) {
            Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> _730_sep = _728_sep;
            Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>>> _731_elems = __default.AppendWithSuffix(elems, _727_elem, _730_sep);
            java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>> _in99 = json;
            Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> _in100 = open;
            Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>>> _in101 = _731_elems;
            json = _in99;
            open = _in100;
            elems = _in101;
            continue TAIL_CALL_START;
          } else if (((_729_s0) == ((short) java.lang.Byte.toUnsignedInt(Std.JSON.ZeroCopy.Deserializer.ArrayParams.__default.CLOSE()))) && (((((_728_sep).dtor_t()).dtor_t()).Length()) == (1))) {
            Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> _732_sep = _728_sep;
            Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>>> _733_elems_k = __default.AppendLast(elems, _727_elem, _732_sep);
            Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>> _734_bracketed = __default.BracketedFromParts(open, _733_elems_k, _732_sep);
            return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), _734_bracketed);
          } else {
            byte _735_separator = __default.SEPARATOR();
            Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _736_pr = Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Failure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>create_ExpectingAnyByte(Std.JSON.Errors.DeserializationError._typeDescriptor(), dafny.DafnySequence.<java.lang.Byte> of(Std.JSON.ZeroCopy.Deserializer.ArrayParams.__default.CLOSE(), _735_separator), _729_s0));
            return _736_pr;
          }
        }
      }
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Bracketed(Std.JSON.Utils.Cursors.Cursor__ cs, java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>> json)
  {
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _737_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.Core.__default.<Std.JSON.Utils.Views.Core.View__>Structural(jopen._typeDescriptor(), cs, __default::Open);
    if ((_737_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
      return (_737_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())));
    } else {
      Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> _738_open = (_737_valueOrError0).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
      Std.JSON.Utils.Cursors.Split<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>>> _739_elems = Std.JSON.Utils.Cursors.Split.<dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>>>create(dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor())), dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>> empty(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor())), (_738_open).dtor_cs());
      if ((((_738_open).dtor_cs()).Peek()) == ((short) java.lang.Byte.toUnsignedInt(Std.JSON.ZeroCopy.Deserializer.ArrayParams.__default.CLOSE()))) {
        java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>> _740_p = __default::Close;
        Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _741_valueOrError1 = Std.JSON.ZeroCopy.Deserializer.Core.__default.<Std.JSON.Utils.Views.Core.View__>Structural(jclose._typeDescriptor(), (_738_open).dtor_cs(), _740_p);
        if ((_741_valueOrError1).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
          return (_741_valueOrError1).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())));
        } else {
          Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> _742_close = (_741_valueOrError1).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
          return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(jopen._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), jclose._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), __default.BracketedFromParts(_738_open, _739_elems, _742_close));
        }
      } else {
        return __default.Elements(json, _738_open, _739_elems);
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
    return "Std.JSON.ZeroCopy.Deserializer.Arrays._default";
  }
}
