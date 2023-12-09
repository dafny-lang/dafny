// Class __default
// Dafny class __default compiled into Java
package Std.JSON.ZeroCopy.Deserializer.Values;

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
import Std.JSON.ZeroCopy.Deserializer.Arrays.*;
import Std.JSON.ZeroCopy.Deserializer.Constants.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Value(Std.JSON.Utils.Cursors.Cursor__ cs) {
    short _745_c = (cs).Peek();
    if ((_745_c) == (((short) ('{')))) {
      Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _746_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.Objects.__default.Object(cs, __default.ValueParser(cs));
      if ((_746_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jlbrace._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), Std.JSON.Grammar.jrbrace._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
        return (_746_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jlbrace._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), Std.JSON.Grammar.jrbrace._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()));
      } else {
        Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>> _let_tmp_rhs32 = (_746_valueOrError0).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jlbrace._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), Std.JSON.Grammar.jrbrace._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
        Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> _747_obj = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>)_let_tmp_rhs32)._t;
        Std.JSON.Utils.Cursors.Cursor__ _748_cs_k = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>)_let_tmp_rhs32)._cs;
        Std.JSON.Grammar.Value _749_v = Std.JSON.Grammar.Value.create_Object(_747_obj);
        Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value> _750_sp = Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>create(Std.JSON.Grammar.Value._typeDescriptor(), _749_v, _748_cs_k);
        return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), _750_sp);
      }
    } else if ((_745_c) == (((short) ('[')))) {
      Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _751_valueOrError1 = Std.JSON.ZeroCopy.Deserializer.Arrays.__default.Array(cs, __default.ValueParser(cs));
      if ((_751_valueOrError1).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jlbracket._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), Std.JSON.Grammar.jrbracket._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
        return (_751_valueOrError1).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jlbracket._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), Std.JSON.Grammar.jrbracket._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()));
      } else {
        Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>> _let_tmp_rhs33 = (_751_valueOrError1).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>_typeDescriptor(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jlbracket._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), Std.JSON.Grammar.jrbracket._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
        Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> _752_arr = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>)_let_tmp_rhs33)._t;
        Std.JSON.Utils.Cursors.Cursor__ _753_cs_k = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>)_let_tmp_rhs33)._cs;
        Std.JSON.Grammar.Value _754_v = Std.JSON.Grammar.Value.create_Array(_752_arr);
        Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value> _755_sp = Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>create(Std.JSON.Grammar.Value._typeDescriptor(), _754_v, _753_cs_k);
        return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), _755_sp);
      }
    } else if ((_745_c) == (((short) ('\"')))) {
      Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jstring>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _756_valueOrError2 = Std.JSON.ZeroCopy.Deserializer.Strings.__default.String(cs);
      if ((_756_valueOrError2).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jstring>_typeDescriptor(Std.JSON.Grammar.jstring._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
        return (_756_valueOrError2).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jstring>_typeDescriptor(Std.JSON.Grammar.jstring._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()));
      } else {
        Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jstring> _let_tmp_rhs34 = (_756_valueOrError2).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jstring>_typeDescriptor(Std.JSON.Grammar.jstring._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
        Std.JSON.Grammar.jstring _757_str = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jstring>)_let_tmp_rhs34)._t;
        Std.JSON.Utils.Cursors.Cursor__ _758_cs_k = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jstring>)_let_tmp_rhs34)._cs;
        return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>create(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.Value.create_String(_757_str), _758_cs_k));
      }
    } else if ((_745_c) == (((short) ('t')))) {
      Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _759_valueOrError3 = Std.JSON.ZeroCopy.Deserializer.Constants.__default.Constant(cs, Std.JSON.Grammar.__default.TRUE());
      if ((_759_valueOrError3).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
        return (_759_valueOrError3).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()));
      } else {
        Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> _let_tmp_rhs35 = (_759_valueOrError3).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
        Std.JSON.Utils.Views.Core.View__ _760_cst = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs35)._t;
        Std.JSON.Utils.Cursors.Cursor__ _761_cs_k = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs35)._cs;
        return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>create(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.Value.create_Bool(_760_cst), _761_cs_k));
      }
    } else if ((_745_c) == (((short) ('f')))) {
      Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _762_valueOrError4 = Std.JSON.ZeroCopy.Deserializer.Constants.__default.Constant(cs, Std.JSON.Grammar.__default.FALSE());
      if ((_762_valueOrError4).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
        return (_762_valueOrError4).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()));
      } else {
        Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> _let_tmp_rhs36 = (_762_valueOrError4).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
        Std.JSON.Utils.Views.Core.View__ _763_cst = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs36)._t;
        Std.JSON.Utils.Cursors.Cursor__ _764_cs_k = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs36)._cs;
        return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>create(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.Value.create_Bool(_763_cst), _764_cs_k));
      }
    } else if ((_745_c) == (((short) ('n')))) {
      Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _765_valueOrError5 = Std.JSON.ZeroCopy.Deserializer.Constants.__default.Constant(cs, Std.JSON.Grammar.__default.NULL());
      if ((_765_valueOrError5).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
        return (_765_valueOrError5).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()));
      } else {
        Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> _let_tmp_rhs37 = (_765_valueOrError5).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
        Std.JSON.Utils.Views.Core.View__ _766_cst = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs37)._t;
        Std.JSON.Utils.Cursors.Cursor__ _767_cs_k = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs37)._cs;
        return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>create(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.Value.create_Null(_766_cst), _767_cs_k));
      }
    } else {
      Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jnumber>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _768_valueOrError6 = Std.JSON.ZeroCopy.Deserializer.Numbers.__default.Number(cs);
      if ((_768_valueOrError6).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jnumber>_typeDescriptor(Std.JSON.Grammar.jnumber._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
        return (_768_valueOrError6).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jnumber>_typeDescriptor(Std.JSON.Grammar.jnumber._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()));
      } else {
        Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jnumber> _let_tmp_rhs38 = (_768_valueOrError6).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jnumber>_typeDescriptor(Std.JSON.Grammar.jnumber._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
        Std.JSON.Grammar.jnumber _769_num = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jnumber>)_let_tmp_rhs38)._t;
        Std.JSON.Utils.Cursors.Cursor__ _770_cs_k = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jnumber>)_let_tmp_rhs38)._cs;
        Std.JSON.Grammar.Value _771_v = Std.JSON.Grammar.Value.create_Number(_769_num);
        Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value> _772_sp = Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>create(Std.JSON.Grammar.Value._typeDescriptor(), _771_v, _770_cs_k);
        return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), _772_sp);
      }
    }
  }
  public static java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>> ValueParser(Std.JSON.Utils.Cursors.Cursor__ cs) {
    java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Boolean> _773_pre = ((java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Boolean>>)(_774_cs) -> ((java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Boolean>)(_775_ps_k_boxed0) -> {
      Std.JSON.Utils.Cursors.Cursor__ _775_ps_k = ((Std.JSON.Utils.Cursors.Cursor__)(java.lang.Object)(_775_ps_k_boxed0));
      return java.lang.Integer.compareUnsigned((_775_ps_k).Length(), (_774_cs).Length()) < 0;
    })).apply(cs);
    java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>> _776_fn = ((java.util.function.Function<java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Boolean>, java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>>>)(_777_pre) -> ((java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Value>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>>)(_778_ps_k_boxed0) -> {
      Std.JSON.Utils.Cursors.Cursor__ _778_ps_k = ((Std.JSON.Utils.Cursors.Cursor__)(java.lang.Object)(_778_ps_k_boxed0));
      return __default.Value(_778_ps_k);
    })).apply(_773_pre);
    return _776_fn;
  }
  @Override
  public java.lang.String toString() {
    return "Std.JSON.ZeroCopy.Deserializer.Values._default";
  }
}
