// Class __default
// Dafny class __default compiled into Java
package Std.JSON.ZeroCopy.Deserializer.Core;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Get(Std.JSON.Utils.Cursors.Cursor__ cs, Std.JSON.Errors.DeserializationError err)
  {
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Cursor__, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _625_valueOrError0 = (cs).<Std.JSON.Errors.DeserializationError>Get(Std.JSON.Errors.DeserializationError._typeDescriptor(), err);
    if ((_625_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
      return (_625_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>>PropagateFailure(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()));
    } else {
      Std.JSON.Utils.Cursors.Cursor__ _626_cs = (_625_valueOrError0).Extract(Std.JSON.Utils.Cursors.Cursor._typeDescriptor(), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
      return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), (_626_cs).Split());
    }
  }
  public static Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> WS(Std.JSON.Utils.Cursors.Cursor__ cs)
  {
    Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> sp = Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>Default(Std.JSON.Grammar.jblanks._typeDescriptor(), Std.JSON.Grammar.jblanks.defaultValue());
    int _627_point_k;
    _627_point_k = (cs).dtor_point();
    int _628_end;
    _628_end = (cs).dtor_end();
    while ((java.lang.Integer.compareUnsigned(_627_point_k, _628_end) < 0) && (Std.JSON.Grammar.__default.Blank_q(((byte)(java.lang.Object)(((cs).dtor_s()).select(_627_point_k)))))) {
      _627_point_k = (int)  ((_627_point_k) + (1));
    }
    sp = (Std.JSON.Utils.Cursors.Cursor__.create((cs).dtor_s(), (cs).dtor_beg(), _627_point_k, (cs).dtor_end())).Split();
    return sp;
  }
  public static <__T> Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<__T>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Structural(dafny.TypeDescriptor<__T> _td___T, Std.JSON.Utils.Cursors.Cursor__ cs, Std.JSON.Utils.Parsers.Parser__<__T, Std.JSON.Errors.DeserializationError> parser)
  {
    Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> _let_tmp_rhs18 = __default.WS(cs);
    Std.JSON.Utils.Views.Core.View__ _629_before = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs18)._t;
    Std.JSON.Utils.Cursors.Cursor__ _630_cs = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs18)._cs;
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<__T>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _631_valueOrError0 = ((Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<__T>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>)(java.lang.Object)(((parser).dtor_fn()).apply(_630_cs)));
    if ((_631_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Split.<__T>_typeDescriptor(_td___T), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
      return (_631_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<__T>>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<__T>_typeDescriptor(_td___T), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<__T>>_typeDescriptor(Std.JSON.Grammar.Structural.<__T>_typeDescriptor(_td___T)));
    } else {
      Std.JSON.Utils.Cursors.Split<__T> _let_tmp_rhs19 = (_631_valueOrError0).Extract(Std.JSON.Utils.Cursors.Split.<__T>_typeDescriptor(_td___T), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
      __T _632_val = ((Std.JSON.Utils.Cursors.Split<__T>)_let_tmp_rhs19)._t;
      Std.JSON.Utils.Cursors.Cursor__ _633_cs = ((Std.JSON.Utils.Cursors.Split<__T>)_let_tmp_rhs19)._cs;
      Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> _let_tmp_rhs20 = __default.WS(_633_cs);
      Std.JSON.Utils.Views.Core.View__ _634_after = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs20)._t;
      Std.JSON.Utils.Cursors.Cursor__ _635_cs = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs20)._cs;
      return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<__T>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<__T>>_typeDescriptor(Std.JSON.Grammar.Structural.<__T>_typeDescriptor(_td___T)), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<__T>>create(Std.JSON.Grammar.Structural.<__T>_typeDescriptor(_td___T), Std.JSON.Grammar.Structural.<__T>create(_td___T, _629_before, _632_val, _634_after), _635_cs));
    }
  }
  public static Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> TryStructural(Std.JSON.Utils.Cursors.Cursor__ cs) {
    Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> _let_tmp_rhs21 = __default.WS(cs);
    Std.JSON.Utils.Views.Core.View__ _636_before = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs21)._t;
    Std.JSON.Utils.Cursors.Cursor__ _637_cs = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs21)._cs;
    Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> _let_tmp_rhs22 = ((_637_cs).SkipByte()).Split();
    Std.JSON.Utils.Views.Core.View__ _638_val = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs22)._t;
    Std.JSON.Utils.Cursors.Cursor__ _639_cs = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs22)._cs;
    Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> _let_tmp_rhs23 = __default.WS(_639_cs);
    Std.JSON.Utils.Views.Core.View__ _640_after = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs23)._t;
    Std.JSON.Utils.Cursors.Cursor__ _641_cs = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs23)._cs;
    return Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>create(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>create(Std.JSON.Utils.Views.Core.View._typeDescriptor(), _636_before, _638_val, _640_after), _641_cs);
  }
  public static java.util.function.Function<Std.JSON.Utils.Views.Core.View__, dafny.DafnySequence<? extends java.lang.Byte>> SpecView()
  {
    return ((java.util.function.Function<Std.JSON.Utils.Views.Core.View__, dafny.DafnySequence<? extends java.lang.Byte>>)(_642_v_boxed0) -> {
      Std.JSON.Utils.Views.Core.View__ _642_v = ((Std.JSON.Utils.Views.Core.View__)(java.lang.Object)(_642_v_boxed0));
      return Std.JSON.ConcreteSyntax.Spec.__default.View(_642_v);
    });
  }
  @Override
  public java.lang.String toString() {
    return "Std.JSON.ZeroCopy.Deserializer.Core._default";
  }
}
