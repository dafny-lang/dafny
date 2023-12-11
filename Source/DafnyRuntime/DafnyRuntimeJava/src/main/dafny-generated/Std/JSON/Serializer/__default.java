// Class __default
// Dafny class __default compiled into Java
package Std.JSON.Serializer;

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
import Std.JavaFileIOInternalExterns.*;
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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static Std.JSON.Utils.Views.Core.View__ Bool(boolean b) {
    return Std.JSON.Utils.Views.Core.View__.OfBytes(((b) ? (Std.JSON.Grammar.__default.TRUE()) : (Std.JSON.Grammar.__default.FALSE())));
  }
  public static <__T> Std.Wrappers.Outcome<Std.JSON.Errors.SerializationError> CheckLength(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> s, Std.JSON.Errors.SerializationError err)
  {
    return Std.Wrappers.Outcome.<Std.JSON.Errors.SerializationError>Need(Std.JSON.Errors.SerializationError._typeDescriptor(), (java.math.BigInteger.valueOf((s).length())).compareTo(Std.BoundedInts.__default.TWO__TO__THE__32()) < 0, err);
  }
  public static Std.Wrappers.Result<Std.JSON.Grammar.jstring, Std.JSON.Errors.SerializationError> String(dafny.DafnySequence<? extends dafny.CodePoint> str) {
    Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError> _430_valueOrError0 = Std.JSON.Spec.__default.EscapeToUTF8(str, java.math.BigInteger.ZERO);
    if ((_430_valueOrError0).IsFailure(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor())) {
      return (_430_valueOrError0).<Std.JSON.Grammar.jstring>PropagateFailure(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.jstring._typeDescriptor());
    } else {
      dafny.DafnySequence<? extends java.lang.Byte> _431_bs = (_430_valueOrError0).Extract(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor());
      Std.Wrappers.Outcome<Std.JSON.Errors.SerializationError> _432_o = __default.<java.lang.Byte>CheckLength(Std.BoundedInts.uint8._typeDescriptor(), _431_bs, Std.JSON.Errors.SerializationError.create_StringTooLong(str));
      if ((_432_o).is_Pass()) {
        return Std.Wrappers.Result.<Std.JSON.Grammar.jstring, Std.JSON.Errors.SerializationError>create_Success(Std.JSON.Grammar.jstring._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.jstring.create(Std.JSON.Grammar.__default.DOUBLEQUOTE(), Std.JSON.Utils.Views.Core.View__.OfBytes(_431_bs), Std.JSON.Grammar.__default.DOUBLEQUOTE()));
      } else {
        return Std.Wrappers.Result.<Std.JSON.Grammar.jstring, Std.JSON.Errors.SerializationError>create_Failure(Std.JSON.Grammar.jstring._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), (_432_o).dtor_error());
      }
    }
  }
  public static Std.JSON.Utils.Views.Core.View__ Sign(java.math.BigInteger n) {
    return Std.JSON.Utils.Views.Core.View__.OfBytes((((n).signum() == -1) ? (dafny.DafnySequence.<java.lang.Byte> of(((byte) ('-')))) : (dafny.DafnySequence.<java.lang.Byte> empty(Std.BoundedInts.uint8._typeDescriptor()))));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> Int_k(java.math.BigInteger n) {
    return Std.JSON.ByteStrConversion.__default.OfInt(n, __default.MINUS());
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Views.Core.View__, Std.JSON.Errors.SerializationError> Int(java.math.BigInteger n) {
    dafny.DafnySequence<? extends java.lang.Byte> _433_bs = __default.Int_k(n);
    Std.Wrappers.Outcome<Std.JSON.Errors.SerializationError> _434_o = __default.<java.lang.Byte>CheckLength(Std.BoundedInts.uint8._typeDescriptor(), _433_bs, Std.JSON.Errors.SerializationError.create_IntTooLarge(n));
    if ((_434_o).is_Pass()) {
      return Std.Wrappers.Result.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Errors.SerializationError>create_Success(Std.JSON.Utils.Views.Core.View._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Utils.Views.Core.View__.OfBytes(_433_bs));
    } else {
      return Std.Wrappers.Result.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Errors.SerializationError>create_Failure(Std.JSON.Utils.Views.Core.View._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), (_434_o).dtor_error());
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Grammar.jnumber, Std.JSON.Errors.SerializationError> Number(Std.JSON.Values.Decimal dec) {
    Std.JSON.Values.Decimal _pat_let_tv2 = dec;
    Std.JSON.Values.Decimal _pat_let_tv3 = dec;
    Std.JSON.Utils.Views.Core.View__ _435_minus = __default.Sign((dec).dtor_n());
    Std.Wrappers.Result<Std.JSON.Utils.Views.Core.View__, Std.JSON.Errors.SerializationError> _436_valueOrError0 = __default.Int(Std.Math.__default.Abs((dec).dtor_n()));
    if ((_436_valueOrError0).IsFailure(Std.JSON.Utils.Views.Core.View._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor())) {
      return (_436_valueOrError0).<Std.JSON.Grammar.jnumber>PropagateFailure(Std.JSON.Utils.Views.Core.View._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.jnumber._typeDescriptor());
    } else {
      Std.JSON.Utils.Views.Core.View__ _437_num = (_436_valueOrError0).Extract(Std.JSON.Utils.Views.Core.View._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor());
      Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jfrac> _438_frac = Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jfrac>create_Empty(Std.JSON.Grammar.jfrac._typeDescriptor());
      Std.Wrappers.Result<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.JSON.Errors.SerializationError> _439_valueOrError1 = ((((dec).dtor_e10()).signum() == 0) ? (Std.Wrappers.Result.<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.JSON.Errors.SerializationError>create_Success(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jexp>_typeDescriptor(Std.JSON.Grammar.jexp._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jexp>create_Empty(Std.JSON.Grammar.jexp._typeDescriptor()))) : (((Std.Wrappers.Result<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.JSON.Errors.SerializationError>)(java.lang.Object)(dafny.Helpers.<Std.JSON.Utils.Views.Core.View__, Std.Wrappers.Result<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.JSON.Errors.SerializationError>>Let(Std.JSON.Utils.Views.Core.View__.OfBytes(dafny.DafnySequence.<java.lang.Byte> of(((byte) ('e')))), boxed2 -> {
        Std.JSON.Utils.Views.Core.View__ _pat_let2_0 = ((Std.JSON.Utils.Views.Core.View__)(java.lang.Object)(boxed2));
        return ((Std.Wrappers.Result<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.JSON.Errors.SerializationError>)(java.lang.Object)(dafny.Helpers.<Std.JSON.Utils.Views.Core.View__, Std.Wrappers.Result<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.JSON.Errors.SerializationError>>Let(_pat_let2_0, boxed3 -> {
          Std.JSON.Utils.Views.Core.View__ _440_e = ((Std.JSON.Utils.Views.Core.View__)(java.lang.Object)(boxed3));
          return ((Std.Wrappers.Result<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.JSON.Errors.SerializationError>)(java.lang.Object)(dafny.Helpers.<Std.JSON.Utils.Views.Core.View__, Std.Wrappers.Result<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.JSON.Errors.SerializationError>>Let(__default.Sign((_pat_let_tv2).dtor_e10()), boxed4 -> {
            Std.JSON.Utils.Views.Core.View__ _pat_let3_0 = ((Std.JSON.Utils.Views.Core.View__)(java.lang.Object)(boxed4));
            return ((Std.Wrappers.Result<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.JSON.Errors.SerializationError>)(java.lang.Object)(dafny.Helpers.<Std.JSON.Utils.Views.Core.View__, Std.Wrappers.Result<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.JSON.Errors.SerializationError>>Let(_pat_let3_0, boxed5 -> {
              Std.JSON.Utils.Views.Core.View__ _441_sign = ((Std.JSON.Utils.Views.Core.View__)(java.lang.Object)(boxed5));
              return ((Std.Wrappers.Result<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.JSON.Errors.SerializationError>)(java.lang.Object)(dafny.Helpers.<Std.Wrappers.Result<Std.JSON.Utils.Views.Core.View__, Std.JSON.Errors.SerializationError>, Std.Wrappers.Result<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.JSON.Errors.SerializationError>>Let(__default.Int(Std.Math.__default.Abs((_pat_let_tv3).dtor_e10())), boxed6 -> {
                Std.Wrappers.Result<Std.JSON.Utils.Views.Core.View__, Std.JSON.Errors.SerializationError> _pat_let4_0 = ((Std.Wrappers.Result<Std.JSON.Utils.Views.Core.View__, Std.JSON.Errors.SerializationError>)(java.lang.Object)(boxed6));
                return ((Std.Wrappers.Result<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.JSON.Errors.SerializationError>)(java.lang.Object)(dafny.Helpers.<Std.Wrappers.Result<Std.JSON.Utils.Views.Core.View__, Std.JSON.Errors.SerializationError>, Std.Wrappers.Result<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.JSON.Errors.SerializationError>>Let(_pat_let4_0, boxed7 -> {
                  Std.Wrappers.Result<Std.JSON.Utils.Views.Core.View__, Std.JSON.Errors.SerializationError> _442_valueOrError2 = ((Std.Wrappers.Result<Std.JSON.Utils.Views.Core.View__, Std.JSON.Errors.SerializationError>)(java.lang.Object)(boxed7));
                  return (((_442_valueOrError2).IsFailure(Std.JSON.Utils.Views.Core.View._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor())) ? ((_442_valueOrError2).<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>>PropagateFailure(Std.JSON.Utils.Views.Core.View._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jexp>_typeDescriptor(Std.JSON.Grammar.jexp._typeDescriptor()))) : (((Std.Wrappers.Result<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.JSON.Errors.SerializationError>)(java.lang.Object)(dafny.Helpers.<Std.JSON.Utils.Views.Core.View__, Std.Wrappers.Result<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.JSON.Errors.SerializationError>>Let((_442_valueOrError2).Extract(Std.JSON.Utils.Views.Core.View._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor()), boxed8 -> {
                    Std.JSON.Utils.Views.Core.View__ _pat_let5_0 = ((Std.JSON.Utils.Views.Core.View__)(java.lang.Object)(boxed8));
                    return ((Std.Wrappers.Result<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.JSON.Errors.SerializationError>)(java.lang.Object)(dafny.Helpers.<Std.JSON.Utils.Views.Core.View__, Std.Wrappers.Result<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.JSON.Errors.SerializationError>>Let(_pat_let5_0, boxed9 -> {
                      Std.JSON.Utils.Views.Core.View__ _443_num = ((Std.JSON.Utils.Views.Core.View__)(java.lang.Object)(boxed9));
                      return Std.Wrappers.Result.<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.JSON.Errors.SerializationError>create_Success(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jexp>_typeDescriptor(Std.JSON.Grammar.jexp._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jexp>create_NonEmpty(Std.JSON.Grammar.jexp._typeDescriptor(), Std.JSON.Grammar.jexp.create(_440_e, _441_sign, _443_num)));
                    }
                    )));
                  }
                  )))));
                }
                )));
              }
              )));
            }
            )));
          }
          )));
        }
        )));
      }
      )))));
      if ((_439_valueOrError1).IsFailure(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jexp>_typeDescriptor(Std.JSON.Grammar.jexp._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor())) {
        return (_439_valueOrError1).<Std.JSON.Grammar.jnumber>PropagateFailure(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jexp>_typeDescriptor(Std.JSON.Grammar.jexp._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.jnumber._typeDescriptor());
      } else {
        Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp> _444_exp = (_439_valueOrError1).Extract(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jexp>_typeDescriptor(Std.JSON.Grammar.jexp._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor());
        return Std.Wrappers.Result.<Std.JSON.Grammar.jnumber, Std.JSON.Errors.SerializationError>create_Success(Std.JSON.Grammar.jnumber._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.jnumber.create(_435_minus, _437_num, Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jfrac>create_Empty(Std.JSON.Grammar.jfrac._typeDescriptor()), _444_exp));
      }
    }
  }
  public static <__T> Std.JSON.Grammar.Structural<__T> MkStructural(dafny.TypeDescriptor<__T> _td___T, __T v)
  {
    return Std.JSON.Grammar.Structural.<__T>create(_td___T, Std.JSON.Grammar.__default.EMPTY(), v, Std.JSON.Grammar.__default.EMPTY());
  }
  public static Std.Wrappers.Result<Std.JSON.Grammar.jKeyValue, Std.JSON.Errors.SerializationError> KeyValue(dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON> kv) {
    Std.Wrappers.Result<Std.JSON.Grammar.jstring, Std.JSON.Errors.SerializationError> _445_valueOrError0 = __default.String((kv).dtor__0());
    if ((_445_valueOrError0).IsFailure(Std.JSON.Grammar.jstring._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor())) {
      return (_445_valueOrError0).<Std.JSON.Grammar.jKeyValue>PropagateFailure(Std.JSON.Grammar.jstring._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor());
    } else {
      Std.JSON.Grammar.jstring _446_k = (_445_valueOrError0).Extract(Std.JSON.Grammar.jstring._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor());
      Std.Wrappers.Result<Std.JSON.Grammar.Value, Std.JSON.Errors.SerializationError> _447_valueOrError1 = __default.Value((kv).dtor__1());
      if ((_447_valueOrError1).IsFailure(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor())) {
        return (_447_valueOrError1).<Std.JSON.Grammar.jKeyValue>PropagateFailure(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor());
      } else {
        Std.JSON.Grammar.Value _448_v = (_447_valueOrError1).Extract(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor());
        return Std.Wrappers.Result.<Std.JSON.Grammar.jKeyValue, Std.JSON.Errors.SerializationError>create_Success(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.jKeyValue.create(_446_k, __default.COLON(), _448_v));
      }
    }
  }
  public static <__D, __S> dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<__D, __S>> MkSuffixedSequence(dafny.TypeDescriptor<__D> _td___D, dafny.TypeDescriptor<__S> _td___S, dafny.DafnySequence<? extends __D> ds, Std.JSON.Grammar.Structural<__S> suffix, java.math.BigInteger start)
  {
    dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<__D, __S>> _449___accumulator = dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<__D, __S>> empty(Std.JSON.Grammar.Suffixed.<__D, __S>_typeDescriptor(_td___D, _td___S));
    TAIL_CALL_START: while (true) {
      if ((start).compareTo(java.math.BigInteger.valueOf((ds).length())) >= 0) {
        return dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<__D, __S>>concatenate(_449___accumulator, dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<__D, __S>> empty(Std.JSON.Grammar.Suffixed.<__D, __S>_typeDescriptor(_td___D, _td___S)));
      } else if (java.util.Objects.equals(start, (java.math.BigInteger.valueOf((ds).length())).subtract(java.math.BigInteger.ONE))) {
        return dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<__D, __S>>concatenate(_449___accumulator, dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<__D, __S>> of(Std.JSON.Grammar.Suffixed.<__D, __S>_typeDescriptor(_td___D, _td___S), Std.JSON.Grammar.Suffixed.<__D, __S>create(_td___D, _td___S, ((__D)(java.lang.Object)((ds).select(dafny.Helpers.toInt((start))))), Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.Structural<__S>>create_Empty(Std.JSON.Grammar.Structural.<__S>_typeDescriptor(_td___S)))));
      } else {
        _449___accumulator = dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<__D, __S>>concatenate(_449___accumulator, dafny.DafnySequence.<Std.JSON.Grammar.Suffixed<__D, __S>> of(Std.JSON.Grammar.Suffixed.<__D, __S>_typeDescriptor(_td___D, _td___S), Std.JSON.Grammar.Suffixed.<__D, __S>create(_td___D, _td___S, ((__D)(java.lang.Object)((ds).select(dafny.Helpers.toInt((start))))), Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.Structural<__S>>create_NonEmpty(Std.JSON.Grammar.Structural.<__S>_typeDescriptor(_td___S), suffix))));
        dafny.DafnySequence<? extends __D> _in77 = ds;
        Std.JSON.Grammar.Structural<__S> _in78 = suffix;
        java.math.BigInteger _in79 = (start).add(java.math.BigInteger.ONE);
        ds = _in77;
        suffix = _in78;
        start = _in79;
        continue TAIL_CALL_START;
      }
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>, Std.JSON.Errors.SerializationError> Object(dafny.DafnySequence<? extends dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>> obj) {
    Std.Wrappers.Result<dafny.DafnySequence<? extends Std.JSON.Grammar.jKeyValue>, Std.JSON.Errors.SerializationError> _450_valueOrError0 = Std.Collections.Seq.__default.<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>, Std.JSON.Grammar.jKeyValue, Std.JSON.Errors.SerializationError>MapWithResult(dafny.Tuple2.<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>_typeDescriptor(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Values.JSON._typeDescriptor()), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), ((java.util.function.Function<dafny.DafnySequence<? extends dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>>, java.util.function.Function<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>, Std.Wrappers.Result<Std.JSON.Grammar.jKeyValue, Std.JSON.Errors.SerializationError>>>)(_451_obj) -> ((java.util.function.Function<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>, Std.Wrappers.Result<Std.JSON.Grammar.jKeyValue, Std.JSON.Errors.SerializationError>>)(_452_v_boxed0) -> {
      dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON> _452_v = ((dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>)(java.lang.Object)(_452_v_boxed0));
      return __default.KeyValue(_452_v);
    })).apply(obj), obj);
    if ((_450_valueOrError0).IsFailure(dafny.DafnySequence.<Std.JSON.Grammar.jKeyValue>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor())) {
      return (_450_valueOrError0).<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>PropagateFailure(dafny.DafnySequence.<Std.JSON.Grammar.jKeyValue>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), Std.JSON.Utils.Views.Core.View._typeDescriptor()));
    } else {
      dafny.DafnySequence<? extends Std.JSON.Grammar.jKeyValue> _453_items = (_450_valueOrError0).Extract(dafny.DafnySequence.<Std.JSON.Grammar.jKeyValue>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor());
      return Std.Wrappers.Result.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>, Std.JSON.Errors.SerializationError>create_Success(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>create(Std.JSON.Utils.Views.Core.View._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), Std.JSON.Utils.Views.Core.View._typeDescriptor(), __default.<Std.JSON.Utils.Views.Core.View__>MkStructural(Std.JSON.Utils.Views.Core.View._typeDescriptor(), Std.JSON.Grammar.__default.LBRACE()), __default.<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>MkSuffixedSequence(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), _453_items, __default.COMMA(), java.math.BigInteger.ZERO), __default.<Std.JSON.Utils.Views.Core.View__>MkStructural(Std.JSON.Utils.Views.Core.View._typeDescriptor(), Std.JSON.Grammar.__default.RBRACE())));
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>, Std.JSON.Errors.SerializationError> Array(dafny.DafnySequence<? extends Std.JSON.Values.JSON> arr) {
    Std.Wrappers.Result<dafny.DafnySequence<? extends Std.JSON.Grammar.Value>, Std.JSON.Errors.SerializationError> _454_valueOrError0 = Std.Collections.Seq.__default.<Std.JSON.Values.JSON, Std.JSON.Grammar.Value, Std.JSON.Errors.SerializationError>MapWithResult(Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), ((java.util.function.Function<dafny.DafnySequence<? extends Std.JSON.Values.JSON>, java.util.function.Function<Std.JSON.Values.JSON, Std.Wrappers.Result<Std.JSON.Grammar.Value, Std.JSON.Errors.SerializationError>>>)(_455_arr) -> ((java.util.function.Function<Std.JSON.Values.JSON, Std.Wrappers.Result<Std.JSON.Grammar.Value, Std.JSON.Errors.SerializationError>>)(_456_v_boxed0) -> {
      Std.JSON.Values.JSON _456_v = ((Std.JSON.Values.JSON)(java.lang.Object)(_456_v_boxed0));
      return __default.Value(_456_v);
    })).apply(arr), arr);
    if ((_454_valueOrError0).IsFailure(dafny.DafnySequence.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor())) {
      return (_454_valueOrError0).<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>>PropagateFailure(dafny.DafnySequence.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), Std.JSON.Utils.Views.Core.View._typeDescriptor()));
    } else {
      dafny.DafnySequence<? extends Std.JSON.Grammar.Value> _457_items = (_454_valueOrError0).Extract(dafny.DafnySequence.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor());
      return Std.Wrappers.Result.<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>, Std.JSON.Errors.SerializationError>create_Success(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>create(Std.JSON.Utils.Views.Core.View._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), Std.JSON.Utils.Views.Core.View._typeDescriptor(), __default.<Std.JSON.Utils.Views.Core.View__>MkStructural(Std.JSON.Utils.Views.Core.View._typeDescriptor(), Std.JSON.Grammar.__default.LBRACKET()), __default.<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>MkSuffixedSequence(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), _457_items, __default.COMMA(), java.math.BigInteger.ZERO), __default.<Std.JSON.Utils.Views.Core.View__>MkStructural(Std.JSON.Utils.Views.Core.View._typeDescriptor(), Std.JSON.Grammar.__default.RBRACKET())));
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Grammar.Value, Std.JSON.Errors.SerializationError> Value(Std.JSON.Values.JSON js) {
    Std.JSON.Values.JSON _source16 = js;
    if (_source16.is_Null()) {
      return Std.Wrappers.Result.<Std.JSON.Grammar.Value, Std.JSON.Errors.SerializationError>create_Success(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.Value.create_Null(Std.JSON.Utils.Views.Core.View__.OfBytes(Std.JSON.Grammar.__default.NULL())));
    } else if (_source16.is_Bool()) {
      boolean _458___mcc_h0 = ((Std.JSON.Values.JSON_Bool)_source16)._b;
      boolean _459_b = _458___mcc_h0;
      return Std.Wrappers.Result.<Std.JSON.Grammar.Value, Std.JSON.Errors.SerializationError>create_Success(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.Value.create_Bool(__default.Bool(_459_b)));
    } else if (_source16.is_String()) {
      dafny.DafnySequence<? extends dafny.CodePoint> _460___mcc_h1 = ((Std.JSON.Values.JSON_String)_source16)._str;
      dafny.DafnySequence<? extends dafny.CodePoint> _461_str = _460___mcc_h1;
      Std.Wrappers.Result<Std.JSON.Grammar.jstring, Std.JSON.Errors.SerializationError> _462_valueOrError0 = __default.String(_461_str);
      if ((_462_valueOrError0).IsFailure(Std.JSON.Grammar.jstring._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor())) {
        return (_462_valueOrError0).<Std.JSON.Grammar.Value>PropagateFailure(Std.JSON.Grammar.jstring._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor());
      } else {
        Std.JSON.Grammar.jstring _463_s = (_462_valueOrError0).Extract(Std.JSON.Grammar.jstring._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor());
        return Std.Wrappers.Result.<Std.JSON.Grammar.Value, Std.JSON.Errors.SerializationError>create_Success(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.Value.create_String(_463_s));
      }
    } else if (_source16.is_Number()) {
      Std.JSON.Values.Decimal _464___mcc_h2 = ((Std.JSON.Values.JSON_Number)_source16)._num;
      Std.JSON.Values.Decimal _465_dec = _464___mcc_h2;
      Std.Wrappers.Result<Std.JSON.Grammar.jnumber, Std.JSON.Errors.SerializationError> _466_valueOrError1 = __default.Number(_465_dec);
      if ((_466_valueOrError1).IsFailure(Std.JSON.Grammar.jnumber._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor())) {
        return (_466_valueOrError1).<Std.JSON.Grammar.Value>PropagateFailure(Std.JSON.Grammar.jnumber._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor());
      } else {
        Std.JSON.Grammar.jnumber _467_n = (_466_valueOrError1).Extract(Std.JSON.Grammar.jnumber._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor());
        return Std.Wrappers.Result.<Std.JSON.Grammar.Value, Std.JSON.Errors.SerializationError>create_Success(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.Value.create_Number(_467_n));
      }
    } else if (_source16.is_Object()) {
      dafny.DafnySequence<? extends dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>> _468___mcc_h3 = ((Std.JSON.Values.JSON_Object)_source16)._obj;
      dafny.DafnySequence<? extends dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>> _469_obj = _468___mcc_h3;
      Std.Wrappers.Result<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>, Std.JSON.Errors.SerializationError> _470_valueOrError2 = __default.Object(_469_obj);
      if ((_470_valueOrError2).IsFailure(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jlbrace._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), Std.JSON.Grammar.jrbrace._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor())) {
        return (_470_valueOrError2).<Std.JSON.Grammar.Value>PropagateFailure(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jlbrace._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), Std.JSON.Grammar.jrbrace._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor());
      } else {
        Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> _471_o = (_470_valueOrError2).Extract(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jlbrace._typeDescriptor(), Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), Std.JSON.Grammar.jrbrace._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor());
        return Std.Wrappers.Result.<Std.JSON.Grammar.Value, Std.JSON.Errors.SerializationError>create_Success(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.Value.create_Object(_471_o));
      }
    } else {
      dafny.DafnySequence<? extends Std.JSON.Values.JSON> _472___mcc_h4 = ((Std.JSON.Values.JSON_Array)_source16)._arr;
      dafny.DafnySequence<? extends Std.JSON.Values.JSON> _473_arr = _472___mcc_h4;
      Std.Wrappers.Result<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>, Std.JSON.Errors.SerializationError> _474_valueOrError3 = __default.Array(_473_arr);
      if ((_474_valueOrError3).IsFailure(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jlbracket._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), Std.JSON.Grammar.jrbracket._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor())) {
        return (_474_valueOrError3).<Std.JSON.Grammar.Value>PropagateFailure(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jlbracket._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), Std.JSON.Grammar.jrbracket._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor());
      } else {
        Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> _475_a = (_474_valueOrError3).Extract(Std.JSON.Grammar.Bracketed.<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jlbracket._typeDescriptor(), Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor(), Std.JSON.Grammar.jrbracket._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor());
        return Std.Wrappers.Result.<Std.JSON.Grammar.Value, Std.JSON.Errors.SerializationError>create_Success(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.Value.create_Array(_475_a));
      }
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>, Std.JSON.Errors.SerializationError> JSON(Std.JSON.Values.JSON js) {
    Std.Wrappers.Result<Std.JSON.Grammar.Value, Std.JSON.Errors.SerializationError> _476_valueOrError0 = __default.Value(js);
    if ((_476_valueOrError0).IsFailure(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor())) {
      return (_476_valueOrError0).<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>>PropagateFailure(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()));
    } else {
      Std.JSON.Grammar.Value _477_val = (_476_valueOrError0).Extract(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor());
      return Std.Wrappers.Result.<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>, Std.JSON.Errors.SerializationError>create_Success(Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), __default.<Std.JSON.Grammar.Value>MkStructural(Std.JSON.Grammar.Value._typeDescriptor(), _477_val));
    }
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> DIGITS()
  {
    return Std.JSON.ByteStrConversion.__default.chars();
  }
  public static byte MINUS()
  {
    return ((byte) ('-'));
  }
  public static Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__> COLON()
  {
    return __default.<Std.JSON.Utils.Views.Core.View__>MkStructural(Std.JSON.Utils.Views.Core.View._typeDescriptor(), Std.JSON.Grammar.__default.COLON());
  }
  public static Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__> COMMA()
  {
    return __default.<Std.JSON.Utils.Views.Core.View__>MkStructural(Std.JSON.Utils.Views.Core.View._typeDescriptor(), Std.JSON.Grammar.__default.COMMA());
  }
  @Override
  public java.lang.String toString() {
    return "Std.JSON.Serializer._default";
  }
}
