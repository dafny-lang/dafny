// Class __default
// Dafny class __default compiled into Java
package Std.JSON.ConcreteSyntax.Spec;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> View(Std.JSON.Utils.Views.Core.View__ v) {
    return (v).Bytes();
  }
  public static <__T> dafny.DafnySequence<? extends java.lang.Byte> Structural(dafny.TypeDescriptor<__T> _td___T, Std.JSON.Grammar.Structural<__T> self, java.util.function.Function<__T, dafny.DafnySequence<? extends java.lang.Byte>> fT)
  {
    return dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(__default.View((self).dtor_before()), ((dafny.DafnySequence<? extends java.lang.Byte>)(java.lang.Object)((fT).apply((self).dtor_t())))), __default.View((self).dtor_after()));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> StructuralView(Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__> self) {
    return __default.<Std.JSON.Utils.Views.Core.View__>Structural(Std.JSON.Utils.Views.Core.View._typeDescriptor(), self, __default::View);
  }
  public static <__T> dafny.DafnySequence<? extends java.lang.Byte> Maybe(dafny.TypeDescriptor<__T> _td___T, Std.JSON.Grammar.Maybe<__T> self, java.util.function.Function<__T, dafny.DafnySequence<? extends java.lang.Byte>> fT)
  {
    if ((self).is_Empty()) {
      return dafny.DafnySequence.<java.lang.Byte> empty(Std.BoundedInts.uint8._typeDescriptor());
    } else {
      return ((dafny.DafnySequence<? extends java.lang.Byte>)(java.lang.Object)((fT).apply((self).dtor_t())));
    }
  }
  public static <__T> dafny.DafnySequence<? extends java.lang.Byte> ConcatBytes(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> ts, java.util.function.Function<__T, dafny.DafnySequence<? extends java.lang.Byte>> fT)
  {
    dafny.DafnySequence<? extends java.lang.Byte> _562___accumulator = dafny.DafnySequence.<java.lang.Byte> empty(Std.BoundedInts.uint8._typeDescriptor());
    TAIL_CALL_START: while (true) {
      if ((java.math.BigInteger.valueOf((ts).length())).signum() == 0) {
        return dafny.DafnySequence.<java.lang.Byte>concatenate(_562___accumulator, dafny.DafnySequence.<java.lang.Byte> empty(Std.BoundedInts.uint8._typeDescriptor()));
      } else {
        _562___accumulator = dafny.DafnySequence.<java.lang.Byte>concatenate(_562___accumulator, ((dafny.DafnySequence<? extends java.lang.Byte>)(java.lang.Object)((fT).apply(((__T)(java.lang.Object)((ts).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))))))));
        dafny.DafnySequence<? extends __T> _in95 = (ts).drop(java.math.BigInteger.ONE);
        java.util.function.Function<__T, dafny.DafnySequence<? extends java.lang.Byte>> _in96 = fT;
        ts = _in95;
        fT = _in96;
        continue TAIL_CALL_START;
      }
    }
  }
  public static <__D, __S> dafny.DafnySequence<? extends java.lang.Byte> Bracketed(dafny.TypeDescriptor<__D> _td___D, dafny.TypeDescriptor<__S> _td___S, Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, __D, __S, Std.JSON.Utils.Views.Core.View__> self, java.util.function.Function<Std.JSON.Grammar.Suffixed<__D, __S>, dafny.DafnySequence<? extends java.lang.Byte>> fDatum)
  {
    return dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(__default.StructuralView((self).dtor_l()), __default.<Std.JSON.Grammar.Suffixed<__D, __S>>ConcatBytes(Std.JSON.Grammar.Suffixed.<__D, __S>_typeDescriptor(_td___D, _td___S), (self).dtor_data(), fDatum)), __default.StructuralView((self).dtor_r()));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> KeyValue(Std.JSON.Grammar.jKeyValue self) {
    return dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(__default.String((self).dtor_k()), __default.StructuralView((self).dtor_colon())), __default.Value((self).dtor_v()));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> Frac(Std.JSON.Grammar.jfrac self) {
    return dafny.DafnySequence.<java.lang.Byte>concatenate(__default.View((self).dtor_period()), __default.View((self).dtor_num()));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> Exp(Std.JSON.Grammar.jexp self) {
    return dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(__default.View((self).dtor_e()), __default.View((self).dtor_sign())), __default.View((self).dtor_num()));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> Number(Std.JSON.Grammar.jnumber self) {
    return dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(__default.View((self).dtor_minus()), __default.View((self).dtor_num())), __default.<Std.JSON.Grammar.jfrac>Maybe(Std.JSON.Grammar.jfrac._typeDescriptor(), (self).dtor_frac(), __default::Frac)), __default.<Std.JSON.Grammar.jexp>Maybe(Std.JSON.Grammar.jexp._typeDescriptor(), (self).dtor_exp(), __default::Exp));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> String(Std.JSON.Grammar.jstring self) {
    return dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(__default.View((self).dtor_lq()), __default.View((self).dtor_contents())), __default.View((self).dtor_rq()));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> CommaSuffix(Std.JSON.Grammar.Maybe<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>> c) {
    return __default.<Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__>>Maybe(Std.JSON.Grammar.Structural.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), c, __default::StructuralView);
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> Member(Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__> self) {
    return dafny.DafnySequence.<java.lang.Byte>concatenate(__default.KeyValue((self).dtor_t()), __default.CommaSuffix((self).dtor_suffix()));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> Item(Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__> self) {
    return dafny.DafnySequence.<java.lang.Byte>concatenate(__default.Value((self).dtor_t()), __default.CommaSuffix((self).dtor_suffix()));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> Object(Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> obj) {
    return __default.<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>Bracketed(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), obj, ((java.util.function.Function<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>, java.util.function.Function<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>, dafny.DafnySequence<? extends java.lang.Byte>>>)(_563_obj) -> ((java.util.function.Function<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>, dafny.DafnySequence<? extends java.lang.Byte>>)(_564_d_boxed0) -> {
      Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__> _564_d = ((Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>)(java.lang.Object)(_564_d_boxed0));
      return __default.Member(_564_d);
    })).apply(obj));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> Array(Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> arr) {
    return __default.<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>Bracketed(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), arr, ((java.util.function.Function<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>, java.util.function.Function<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>, dafny.DafnySequence<? extends java.lang.Byte>>>)(_565_arr) -> ((java.util.function.Function<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>, dafny.DafnySequence<? extends java.lang.Byte>>)(_566_d_boxed0) -> {
      Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__> _566_d = ((Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>)(java.lang.Object)(_566_d_boxed0));
      return __default.Item(_566_d);
    })).apply(arr));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> Value(Std.JSON.Grammar.Value self) {
    Std.JSON.Grammar.Value _source22 = self;
    if (_source22.is_Null()) {
      Std.JSON.Utils.Views.Core.View__ _567___mcc_h0 = ((Std.JSON.Grammar.Value_Null)_source22)._n;
      Std.JSON.Utils.Views.Core.View__ _568_n = _567___mcc_h0;
      return __default.View(_568_n);
    } else if (_source22.is_Bool()) {
      Std.JSON.Utils.Views.Core.View__ _569___mcc_h1 = ((Std.JSON.Grammar.Value_Bool)_source22)._b;
      Std.JSON.Utils.Views.Core.View__ _570_b = _569___mcc_h1;
      return __default.View(_570_b);
    } else if (_source22.is_String()) {
      Std.JSON.Grammar.jstring _571___mcc_h2 = ((Std.JSON.Grammar.Value_String)_source22)._str;
      Std.JSON.Grammar.jstring _572_str = _571___mcc_h2;
      return __default.String(_572_str);
    } else if (_source22.is_Number()) {
      Std.JSON.Grammar.jnumber _573___mcc_h3 = ((Std.JSON.Grammar.Value_Number)_source22)._num;
      Std.JSON.Grammar.jnumber _574_num = _573___mcc_h3;
      return __default.Number(_574_num);
    } else if (_source22.is_Object()) {
      Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> _575___mcc_h4 = ((Std.JSON.Grammar.Value_Object)_source22)._obj;
      Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> _576_obj = _575___mcc_h4;
      return __default.Object(_576_obj);
    } else {
      Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> _577___mcc_h5 = ((Std.JSON.Grammar.Value_Array)_source22)._arr;
      Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> _578_arr = _577___mcc_h5;
      return __default.Array(_578_arr);
    }
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> JSON(Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value> js) {
    return __default.<Std.JSON.Grammar.Value>Structural(Std.JSON.Grammar.Value._typeDescriptor(), js, __default::Value);
  }
  @Override
  public java.lang.String toString() {
    return "Std.JSON.ConcreteSyntax.Spec._default";
  }
}
