// Class __default
// Dafny class __default compiled into Java
package Std.JSON.ZeroCopy.Deserializer.ObjectParams;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Colon(Std.JSON.Utils.Cursors.Cursor__ cs) {
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Cursor__, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _676_valueOrError0 = (cs).<Std.JSON.Errors.DeserializationError>AssertChar(Std.JSON.Errors.DeserializationError._typeDescriptor(), ':');
    if ((_676_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
      return (_676_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>>PropagateFailure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()));
    } else {
      Std.JSON.Utils.Cursors.Cursor__ _677_cs = (_676_valueOrError0).Extract(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
      return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), (_677_cs).Split());
    }
  }
  public static Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jKeyValue> KeyValueFromParts(Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jstring> k, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> colon, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value> v)
  {
    Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jKeyValue> _678_sp = Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jKeyValue>create(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jKeyValue.create((k).dtor_t(), (colon).dtor_t(), (v).dtor_t()), (v).dtor_cs());
    return _678_sp;
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> ElementSpec(Std.JSON.Grammar.jKeyValue t) {
    return Std.JSON.ConcreteSyntax.Spec.__default.KeyValue(t);
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jKeyValue>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Element(Std.JSON.Utils.Cursors.Cursor__ cs, java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>> json)
  {
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jstring>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _679_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.Strings.__default.String(cs);
    if ((_679_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jstring>_typeDescriptor(Std.JSON.Grammar.jstring._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
      return (_679_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jKeyValue>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jstring>_typeDescriptor(Std.JSON.Grammar.jstring._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jKeyValue>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor()));
    } else {
      Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jstring> _680_k = (_679_valueOrError0).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jstring>_typeDescriptor(Std.JSON.Grammar.jstring._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
      java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>> _681_p = __default::Colon;
      Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _682_valueOrError1 = Std.JSON.ZeroCopy.Deserializer.Core.__default.<Std.JSON.Utils.Views.Core.View__>Structural(Std.JSON.Grammar.jcolon._typeDescriptor(), (_680_k).dtor_cs(), _681_p);
      if ((_682_valueOrError1).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jcolon._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
        return (_682_valueOrError1).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jKeyValue>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jcolon._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jKeyValue>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor()));
      } else {
        Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> _683_colon = (_682_valueOrError1).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jcolon._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
        Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _684_valueOrError2 = ((Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>)(java.lang.Object)(((json)).apply((_683_colon).dtor_cs())));
        if ((_684_valueOrError2).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
          return (_684_valueOrError2).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jKeyValue>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jKeyValue>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor()));
        } else {
          Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value> _685_v = (_684_valueOrError2).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
          Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jKeyValue> _686_kv = __default.KeyValueFromParts(_680_k, _683_colon, _685_v);
          return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jKeyValue>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jKeyValue>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), _686_kv);
        }
      }
    }
  }
  public static byte OPEN()
  {
    return ((byte) ('{'));
  }
  public static byte CLOSE()
  {
    return ((byte) ('}'));
  }
  @Override
  public java.lang.String toString() {
    return "Std.JSON.ZeroCopy.Deserializer.ObjectParams._default";
  }
}
