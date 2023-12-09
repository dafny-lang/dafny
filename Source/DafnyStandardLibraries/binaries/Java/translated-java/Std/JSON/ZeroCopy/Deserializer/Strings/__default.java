// Class __default
// Dafny class __default compiled into Java
package Std.JSON.ZeroCopy.Deserializer.Strings;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Cursor__, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> StringBody(Std.JSON.Utils.Cursors.Cursor__ cs)
  {
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Cursor__, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> pr = Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Cursor__, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>Default(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Cursor.defaultValue());
    boolean _634_escaped;
    _634_escaped = false;
    int _hi3 = (cs).dtor_end();
    for (int _635_point_k = (cs).dtor_point(); java.lang.Integer.compareUnsigned(_635_point_k, _hi3) < 0; _635_point_k++) {
      byte _636_byte;
      _636_byte = ((byte)(java.lang.Object)(((cs).dtor_s()).select(_635_point_k)));
      if (((_636_byte) == (((byte) ('\"')))) && (!(_634_escaped))) {
        pr = Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Cursor__, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Cursor__._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Cursor__.create((cs).dtor_s(), (cs).dtor_beg(), _635_point_k, (cs).dtor_end()));
        return pr;
      } else if ((_636_byte) == (((byte) ('\\')))) {
        _634_escaped = !(_634_escaped);
      } else {
        _634_escaped = false;
      }
    }
    pr = Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Cursor__, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Failure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>create_EOF(Std.JSON.Errors.DeserializationError._typeDescriptor()));
    return pr;
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Quote(Std.JSON.Utils.Cursors.Cursor__ cs) {
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Cursor__, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _637_valueOrError0 = (cs).<Std.JSON.Errors.DeserializationError>AssertChar(Std.JSON.Errors.DeserializationError._typeDescriptor(), '\"');
    if ((_637_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
      return (_637_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>>PropagateFailure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()));
    } else {
      Std.JSON.Utils.Cursors.Cursor__ _638_cs = (_637_valueOrError0).Extract(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
      return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), (_638_cs).Split());
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jstring>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> String(Std.JSON.Utils.Cursors.Cursor__ cs) {
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _639_valueOrError0 = __default.Quote(cs);
    if ((_639_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jquote._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
      return (_639_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jstring>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jquote._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jstring>_typeDescriptor(Std.JSON.Grammar.jstring._typeDescriptor()));
    } else {
      Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> _let_tmp_rhs24 = (_639_valueOrError0).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jquote._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
      Std.JSON.Utils.Views.Core.View__ _640_lq = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs24)._t;
      Std.JSON.Utils.Cursors.Cursor__ _641_cs = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs24)._cs;
      Std.Wrappers.Result<Std.JSON.Utils.Cursors.Cursor__, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _642_valueOrError1 = __default.StringBody(_641_cs);
      if ((_642_valueOrError1).IsFailure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
        return (_642_valueOrError1).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jstring>>PropagateFailure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jstring>_typeDescriptor(Std.JSON.Grammar.jstring._typeDescriptor()));
      } else {
        Std.JSON.Utils.Cursors.Cursor__ _643_contents = (_642_valueOrError1).Extract(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
        Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> _let_tmp_rhs25 = (_643_contents).Split();
        Std.JSON.Utils.Views.Core.View__ _644_contents = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs25)._t;
        Std.JSON.Utils.Cursors.Cursor__ _645_cs = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs25)._cs;
        Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _646_valueOrError2 = __default.Quote(_645_cs);
        if ((_646_valueOrError2).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jquote._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
          return (_646_valueOrError2).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jstring>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jquote._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jstring>_typeDescriptor(Std.JSON.Grammar.jstring._typeDescriptor()));
        } else {
          Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> _let_tmp_rhs26 = (_646_valueOrError2).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jquote._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
          Std.JSON.Utils.Views.Core.View__ _647_rq = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs26)._t;
          Std.JSON.Utils.Cursors.Cursor__ _648_cs = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs26)._cs;
          return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jstring>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jstring>_typeDescriptor(Std.JSON.Grammar.jstring._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jstring>create(Std.JSON.Grammar.jstring._typeDescriptor(), Std.JSON.Grammar.jstring.create(_640_lq, _644_contents, _647_rq), _648_cs));
        }
      }
    }
  }
  @Override
  public java.lang.String toString() {
    return "Std.JSON.ZeroCopy.Deserializer.Strings._default";
  }
}
