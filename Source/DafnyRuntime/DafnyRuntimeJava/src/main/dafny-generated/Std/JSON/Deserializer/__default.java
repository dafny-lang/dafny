// Class __default
// Dafny class __default compiled into Java
package Std.JSON.Deserializer;

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
import Std.JSON.Serializer.*;
import Std.JSON.Deserializer.Uint16StrConversion.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static boolean Bool(Std.JSON.Utils.Views.Core.View__ js) {
    return ((js).At(0)) == (((byte) ('t')));
  }
  public static Std.JSON.Errors.DeserializationError UnsupportedEscape16(dafny.DafnySequence<? extends java.lang.Short> code) {
    return Std.JSON.Errors.DeserializationError.create_UnsupportedEscape((Std.Unicode.UnicodeStringsWithUnicodeChar.__default.FromUTF16Checked(code)).GetOr(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), dafny.DafnySequence.asUnicodeString("Couldn't decode UTF-16")));
  }
  public static short ToNat16(dafny.DafnySequence<? extends java.lang.Short> str) {
    java.math.BigInteger _496_hd = Std.JSON.Deserializer.Uint16StrConversion.__default.ToNat(str);
    return (_496_hd).shortValue();
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Short>, Std.JSON.Errors.DeserializationError> Unescape(dafny.DafnySequence<? extends java.lang.Short> str, java.math.BigInteger start, dafny.DafnySequence<? extends java.lang.Short> prefix)
  {
    TAIL_CALL_START: while (true) {
      if ((start).compareTo(java.math.BigInteger.valueOf((str).length())) >= 0) {
        return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Short>, Std.JSON.Errors.DeserializationError>create_Success(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), prefix);
      } else if ((((short)(java.lang.Object)((str).select(dafny.Helpers.toInt((start)))))) == (((short) ('\\')))) {
        if (java.util.Objects.equals(java.math.BigInteger.valueOf((str).length()), (start).add(java.math.BigInteger.ONE))) {
          return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Short>, Std.JSON.Errors.DeserializationError>create_Failure(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Errors.DeserializationError.create_EscapeAtEOS());
        } else {
          short _497_c = ((short)(java.lang.Object)((str).select(dafny.Helpers.toInt(((start).add(java.math.BigInteger.ONE))))));
          if ((_497_c) == (((short) ('u')))) {
            if ((java.math.BigInteger.valueOf((str).length())).compareTo((start).add(java.math.BigInteger.valueOf(6L))) <= 0) {
              return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Short>, Std.JSON.Errors.DeserializationError>create_Failure(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Errors.DeserializationError.create_EscapeAtEOS());
            } else {
              dafny.DafnySequence<? extends java.lang.Short> _498_code = (str).subsequence(dafny.Helpers.toInt(((start).add(java.math.BigInteger.valueOf(2L)))), dafny.Helpers.toInt(((start).add(java.math.BigInteger.valueOf(6L)))));
              if (((java.util.function.Function<dafny.DafnySequence<? extends java.lang.Short>, Boolean>)(_499_code) -> dafny.Helpers.Quantifier((_499_code).UniqueElements(), false, ((_exists_var_0_boxed0) -> {
                short _exists_var_0 = ((short)(java.lang.Object)(_exists_var_0_boxed0));
                if (true) {
                  short _500_c = (short)_exists_var_0;
                  return ((_499_code).contains(_500_c)) && (!(__default.HEX__TABLE__16()).<java.lang.Short>contains(_500_c));
                } else {
                  return false;
                }
              }))).apply(_498_code)) {
                return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Short>, Std.JSON.Errors.DeserializationError>create_Failure(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), __default.UnsupportedEscape16(_498_code));
              } else {
                short _501_hd = __default.ToNat16(_498_code);
                dafny.DafnySequence<? extends java.lang.Short> _in85 = str;
                java.math.BigInteger _in86 = (start).add(java.math.BigInteger.valueOf(6L));
                dafny.DafnySequence<? extends java.lang.Short> _in87 = dafny.DafnySequence.<java.lang.Short>concatenate(prefix, dafny.DafnySequence.<java.lang.Short> of(_501_hd));
                str = _in85;
                start = _in86;
                prefix = _in87;
                continue TAIL_CALL_START;
              }
            }
          } else {
            short _502_unescaped = (((_497_c) == ((short) 34)) ? ((short) 34) : ((((_497_c) == ((short) 92)) ? ((short) 92) : ((((_497_c) == ((short) 98)) ? ((short) 8) : ((((_497_c) == ((short) 102)) ? ((short) 12) : ((((_497_c) == ((short) 110)) ? ((short) 10) : ((((_497_c) == ((short) 114)) ? ((short) 13) : ((((_497_c) == ((short) 116)) ? ((short) 9) : ((short) 0))))))))))))));
            if ((dafny.Helpers.unsignedToBigInteger(_502_unescaped)).signum() == 0) {
              return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Short>, Std.JSON.Errors.DeserializationError>create_Failure(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), __default.UnsupportedEscape16((str).subsequence(dafny.Helpers.toInt((start)), dafny.Helpers.toInt(((start).add(java.math.BigInteger.valueOf(2L)))))));
            } else {
              dafny.DafnySequence<? extends java.lang.Short> _in88 = str;
              java.math.BigInteger _in89 = (start).add(java.math.BigInteger.valueOf(2L));
              dafny.DafnySequence<? extends java.lang.Short> _in90 = dafny.DafnySequence.<java.lang.Short>concatenate(prefix, dafny.DafnySequence.<java.lang.Short> of(_502_unescaped));
              str = _in88;
              start = _in89;
              prefix = _in90;
              continue TAIL_CALL_START;
            }
          }
        }
      } else {
        dafny.DafnySequence<? extends java.lang.Short> _in91 = str;
        java.math.BigInteger _in92 = (start).add(java.math.BigInteger.ONE);
        dafny.DafnySequence<? extends java.lang.Short> _in93 = dafny.DafnySequence.<java.lang.Short>concatenate(prefix, dafny.DafnySequence.<java.lang.Short> of(((short)(java.lang.Object)((str).select(dafny.Helpers.toInt((start)))))));
        str = _in91;
        start = _in92;
        prefix = _in93;
        continue TAIL_CALL_START;
      }
    }
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Errors.DeserializationError> String(Std.JSON.Grammar.jstring js) {
    Std.Wrappers.Result<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Errors.DeserializationError> _503_valueOrError0 = (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.FromUTF8Checked(((js).dtor_contents()).Bytes())).<Std.JSON.Errors.DeserializationError>ToResult(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Errors.DeserializationError.create_InvalidUnicode());
    if ((_503_valueOrError0).IsFailure(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor())) {
      return (_503_valueOrError0).<dafny.DafnySequence<? extends dafny.CodePoint>>PropagateFailure(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor(), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR));
    } else {
      dafny.DafnySequence<? extends dafny.CodePoint> _504_asUtf32 = (_503_valueOrError0).Extract(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor());
      Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Short>, Std.JSON.Errors.DeserializationError> _505_valueOrError1 = (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ToUTF16Checked(_504_asUtf32)).<Std.JSON.Errors.DeserializationError>ToResult(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Errors.DeserializationError.create_InvalidUnicode());
      if ((_505_valueOrError1).IsFailure(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor())) {
        return (_505_valueOrError1).<dafny.DafnySequence<? extends dafny.CodePoint>>PropagateFailure(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR));
      } else {
        dafny.DafnySequence<? extends java.lang.Short> _506_asUint16 = (_505_valueOrError1).Extract(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor());
        Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Short>, Std.JSON.Errors.DeserializationError> _507_valueOrError2 = __default.Unescape(_506_asUint16, java.math.BigInteger.ZERO, dafny.DafnySequence.<java.lang.Short> empty(Std.BoundedInts.uint16._typeDescriptor()));
        if ((_507_valueOrError2).IsFailure(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor())) {
          return (_507_valueOrError2).<dafny.DafnySequence<? extends dafny.CodePoint>>PropagateFailure(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR));
        } else {
          dafny.DafnySequence<? extends java.lang.Short> _508_unescaped = (_507_valueOrError2).Extract(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor());
          return (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.FromUTF16Checked(_508_unescaped)).<Std.JSON.Errors.DeserializationError>ToResult(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Errors.DeserializationError.create_InvalidUnicode());
        }
      }
    }
  }
  public static Std.Wrappers.Result<java.math.BigInteger, Std.JSON.Errors.DeserializationError> ToInt(Std.JSON.Utils.Views.Core.View__ sign, Std.JSON.Utils.Views.Core.View__ n)
  {
    java.math.BigInteger _509_n = Std.JSON.ByteStrConversion.__default.ToNat((n).Bytes());
    return Std.Wrappers.Result.<java.math.BigInteger, Std.JSON.Errors.DeserializationError>create_Success(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor(), (((sign).Char_q('-')) ? ((java.math.BigInteger.ZERO).subtract(_509_n)) : (_509_n)));
  }
  public static Std.Wrappers.Result<Std.JSON.Values.Decimal, Std.JSON.Errors.DeserializationError> Number(Std.JSON.Grammar.jnumber js) {
    Std.JSON.Grammar.jnumber _let_tmp_rhs17 = js;
    Std.JSON.Utils.Views.Core.View__ _510_minus = ((Std.JSON.Grammar.jnumber)_let_tmp_rhs17)._minus;
    Std.JSON.Utils.Views.Core.View__ _511_num = ((Std.JSON.Grammar.jnumber)_let_tmp_rhs17)._num;
    Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jfrac> _512_frac = ((Std.JSON.Grammar.jnumber)_let_tmp_rhs17)._frac;
    Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp> _513_exp = ((Std.JSON.Grammar.jnumber)_let_tmp_rhs17)._exp;
    Std.Wrappers.Result<java.math.BigInteger, Std.JSON.Errors.DeserializationError> _514_valueOrError0 = __default.ToInt(_510_minus, _511_num);
    if ((_514_valueOrError0).IsFailure(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor())) {
      return (_514_valueOrError0).<Std.JSON.Values.Decimal>PropagateFailure(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.Decimal._typeDescriptor());
    } else {
      java.math.BigInteger _515_n = (_514_valueOrError0).Extract(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor());
      Std.Wrappers.Result<java.math.BigInteger, Std.JSON.Errors.DeserializationError> _516_valueOrError1 = ((java.util.function.Function<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.Wrappers.Result<java.math.BigInteger, Std.JSON.Errors.DeserializationError>>)(_source17_boxed0) -> {
        Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp> _source17 = ((Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>)(java.lang.Object)(_source17_boxed0));
        if (_source17.is_Empty()) {
          return Std.Wrappers.Result.<java.math.BigInteger, Std.JSON.Errors.DeserializationError>create_Success(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor(), java.math.BigInteger.ZERO);
        } else {
          Std.JSON.Grammar.jexp _517___mcc_h0 = ((Std.JSON.Grammar.Maybe_NonEmpty<Std.JSON.Grammar.jexp>)_source17)._t;
          Std.JSON.Grammar.jexp _source18 = _517___mcc_h0;
          Std.JSON.Utils.Views.Core.View__ _518___mcc_h1 = ((Std.JSON.Grammar.jexp)_source18)._e;
          Std.JSON.Utils.Views.Core.View__ _519___mcc_h2 = ((Std.JSON.Grammar.jexp)_source18)._sign;
          Std.JSON.Utils.Views.Core.View__ _520___mcc_h3 = ((Std.JSON.Grammar.jexp)_source18)._num;
          Std.JSON.Utils.Views.Core.View__ _521_num = _520___mcc_h3;
          Std.JSON.Utils.Views.Core.View__ _522_sign = _519___mcc_h2;
          return __default.ToInt(_522_sign, _521_num);
        }
      }).apply(_513_exp);
      if ((_516_valueOrError1).IsFailure(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor())) {
        return (_516_valueOrError1).<Std.JSON.Values.Decimal>PropagateFailure(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.Decimal._typeDescriptor());
      } else {
        java.math.BigInteger _523_e10 = (_516_valueOrError1).Extract(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor());
        Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jfrac> _source19 = _512_frac;
        if (_source19.is_Empty()) {
          return Std.Wrappers.Result.<Std.JSON.Values.Decimal, Std.JSON.Errors.DeserializationError>create_Success(Std.JSON.Values.Decimal._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.Decimal.create(_515_n, _523_e10));
        } else {
          Std.JSON.Grammar.jfrac _524___mcc_h4 = ((Std.JSON.Grammar.Maybe_NonEmpty<Std.JSON.Grammar.jfrac>)_source19)._t;
          Std.JSON.Grammar.jfrac _source20 = _524___mcc_h4;
          Std.JSON.Utils.Views.Core.View__ _525___mcc_h5 = ((Std.JSON.Grammar.jfrac)_source20)._period;
          Std.JSON.Utils.Views.Core.View__ _526___mcc_h6 = ((Std.JSON.Grammar.jfrac)_source20)._num;
          Std.JSON.Utils.Views.Core.View__ _527_num = _526___mcc_h6;
          java.math.BigInteger _528_pow10 = dafny.Helpers.unsignedToBigInteger((_527_num).Length());
          Std.Wrappers.Result<java.math.BigInteger, Std.JSON.Errors.DeserializationError> _529_valueOrError2 = __default.ToInt(_510_minus, _527_num);
          if ((_529_valueOrError2).IsFailure(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor())) {
            return (_529_valueOrError2).<Std.JSON.Values.Decimal>PropagateFailure(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.Decimal._typeDescriptor());
          } else {
            java.math.BigInteger _530_frac = (_529_valueOrError2).Extract(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor());
            return Std.Wrappers.Result.<Std.JSON.Values.Decimal, Std.JSON.Errors.DeserializationError>create_Success(Std.JSON.Values.Decimal._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.Decimal.create(((_515_n).multiply(Std.Arithmetic.Power.__default.Pow(java.math.BigInteger.valueOf(10L), _528_pow10))).add(_530_frac), (_523_e10).subtract(_528_pow10)));
          }
        }
      }
    }
  }
  public static Std.Wrappers.Result<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>, Std.JSON.Errors.DeserializationError> KeyValue(Std.JSON.Grammar.jKeyValue js) {
    Std.Wrappers.Result<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Errors.DeserializationError> _531_valueOrError0 = __default.String((js).dtor_k());
    if ((_531_valueOrError0).IsFailure(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor())) {
      return (_531_valueOrError0).<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>>PropagateFailure(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor(), dafny.Tuple2.<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>_typeDescriptor(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Values.JSON._typeDescriptor()));
    } else {
      dafny.DafnySequence<? extends dafny.CodePoint> _532_k = (_531_valueOrError0).Extract(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor());
      Std.Wrappers.Result<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError> _533_valueOrError1 = __default.Value((js).dtor_v());
      if ((_533_valueOrError1).IsFailure(Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor())) {
        return (_533_valueOrError1).<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>>PropagateFailure(Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), dafny.Tuple2.<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>_typeDescriptor(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Values.JSON._typeDescriptor()));
      } else {
        Std.JSON.Values.JSON _534_v = (_533_valueOrError1).Extract(Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor());
        return Std.Wrappers.Result.<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>, Std.JSON.Errors.DeserializationError>create_Success(dafny.Tuple2.<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>_typeDescriptor(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Values.JSON._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), dafny.Tuple2.<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>create(_532_k, _534_v));
      }
    }
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>>, Std.JSON.Errors.DeserializationError> Object(Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> js) {
    return Std.Collections.Seq.__default.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>, dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>, Std.JSON.Errors.DeserializationError>MapWithResult(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor()), dafny.Tuple2.<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>_typeDescriptor(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Values.JSON._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), ((java.util.function.Function<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>, java.util.function.Function<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>, Std.Wrappers.Result<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>, Std.JSON.Errors.DeserializationError>>>)(_535_js) -> ((java.util.function.Function<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>, Std.Wrappers.Result<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>, Std.JSON.Errors.DeserializationError>>)(_536_d_boxed0) -> {
      Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__> _536_d = ((Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>)(java.lang.Object)(_536_d_boxed0));
      return __default.KeyValue((_536_d).dtor_t());
    })).apply(js), (js).dtor_data());
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends Std.JSON.Values.JSON>, Std.JSON.Errors.DeserializationError> Array(Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> js) {
    return Std.Collections.Seq.__default.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>, Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError>MapWithResult(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor()), Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), ((java.util.function.Function<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>, java.util.function.Function<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>, Std.Wrappers.Result<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError>>>)(_537_js) -> ((java.util.function.Function<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>, Std.Wrappers.Result<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError>>)(_538_d_boxed0) -> {
      Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__> _538_d = ((Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>)(java.lang.Object)(_538_d_boxed0));
      return __default.Value((_538_d).dtor_t());
    })).apply(js), (js).dtor_data());
  }
  public static Std.Wrappers.Result<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError> Value(Std.JSON.Grammar.Value js) {
    Std.JSON.Grammar.Value _source21 = js;
    if (_source21.is_Null()) {
      Std.JSON.Utils.Views.Core.View__ _539___mcc_h0 = ((Std.JSON.Grammar.Value_Null)_source21)._n;
      return Std.Wrappers.Result.<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError>create_Success(Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON.create_Null());
    } else if (_source21.is_Bool()) {
      Std.JSON.Utils.Views.Core.View__ _540___mcc_h1 = ((Std.JSON.Grammar.Value_Bool)_source21)._b;
      Std.JSON.Utils.Views.Core.View__ _541_b = _540___mcc_h1;
      return Std.Wrappers.Result.<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError>create_Success(Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON.create_Bool(__default.Bool(_541_b)));
    } else if (_source21.is_String()) {
      Std.JSON.Grammar.jstring _542___mcc_h2 = ((Std.JSON.Grammar.Value_String)_source21)._str;
      Std.JSON.Grammar.jstring _543_str = _542___mcc_h2;
      Std.Wrappers.Result<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Errors.DeserializationError> _544_valueOrError0 = __default.String(_543_str);
      if ((_544_valueOrError0).IsFailure(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor())) {
        return (_544_valueOrError0).<Std.JSON.Values.JSON>PropagateFailure(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON._typeDescriptor());
      } else {
        dafny.DafnySequence<? extends dafny.CodePoint> _545_s = (_544_valueOrError0).Extract(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor());
        return Std.Wrappers.Result.<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError>create_Success(Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON.create_String(_545_s));
      }
    } else if (_source21.is_Number()) {
      Std.JSON.Grammar.jnumber _546___mcc_h3 = ((Std.JSON.Grammar.Value_Number)_source21)._num;
      Std.JSON.Grammar.jnumber _547_dec = _546___mcc_h3;
      Std.Wrappers.Result<Std.JSON.Values.Decimal, Std.JSON.Errors.DeserializationError> _548_valueOrError1 = __default.Number(_547_dec);
      if ((_548_valueOrError1).IsFailure(Std.JSON.Values.Decimal._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor())) {
        return (_548_valueOrError1).<Std.JSON.Values.JSON>PropagateFailure(Std.JSON.Values.Decimal._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON._typeDescriptor());
      } else {
        Std.JSON.Values.Decimal _549_n = (_548_valueOrError1).Extract(Std.JSON.Values.Decimal._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor());
        return Std.Wrappers.Result.<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError>create_Success(Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON.create_Number(_549_n));
      }
    } else if (_source21.is_Object()) {
      Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> _550___mcc_h4 = ((Std.JSON.Grammar.Value_Object)_source21)._obj;
      Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> _551_obj = _550___mcc_h4;
      Std.Wrappers.Result<dafny.DafnySequence<? extends dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>>, Std.JSON.Errors.DeserializationError> _552_valueOrError2 = __default.Object(_551_obj);
      if ((_552_valueOrError2).IsFailure(dafny.DafnySequence.<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>>_typeDescriptor(dafny.Tuple2.<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>_typeDescriptor(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Values.JSON._typeDescriptor())), Std.JSON.Errors.DeserializationError._typeDescriptor())) {
        return (_552_valueOrError2).<Std.JSON.Values.JSON>PropagateFailure(dafny.DafnySequence.<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>>_typeDescriptor(dafny.Tuple2.<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>_typeDescriptor(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Values.JSON._typeDescriptor())), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON._typeDescriptor());
      } else {
        dafny.DafnySequence<? extends dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>> _553_o = (_552_valueOrError2).Extract(dafny.DafnySequence.<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>>_typeDescriptor(dafny.Tuple2.<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>_typeDescriptor(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Values.JSON._typeDescriptor())), Std.JSON.Errors.DeserializationError._typeDescriptor());
        return Std.Wrappers.Result.<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError>create_Success(Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON.create_Object(_553_o));
      }
    } else {
      Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> _554___mcc_h5 = ((Std.JSON.Grammar.Value_Array)_source21)._arr;
      Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> _555_arr = _554___mcc_h5;
      Std.Wrappers.Result<dafny.DafnySequence<? extends Std.JSON.Values.JSON>, Std.JSON.Errors.DeserializationError> _556_valueOrError3 = __default.Array(_555_arr);
      if ((_556_valueOrError3).IsFailure(dafny.DafnySequence.<Std.JSON.Values.JSON>_typeDescriptor(Std.JSON.Values.JSON._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor())) {
        return (_556_valueOrError3).<Std.JSON.Values.JSON>PropagateFailure(dafny.DafnySequence.<Std.JSON.Values.JSON>_typeDescriptor(Std.JSON.Values.JSON._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON._typeDescriptor());
      } else {
        dafny.DafnySequence<? extends Std.JSON.Values.JSON> _557_a = (_556_valueOrError3).Extract(dafny.DafnySequence.<Std.JSON.Values.JSON>_typeDescriptor(Std.JSON.Values.JSON._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor());
        return Std.Wrappers.Result.<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError>create_Success(Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON.create_Array(_557_a));
      }
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError> JSON(Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value> js) {
    return __default.Value((js).dtor_t());
  }
  public static dafny.DafnyMap<? extends java.lang.Short, ? extends java.math.BigInteger> HEX__TABLE__16()
  {
    return Std.JSON.Deserializer.Uint16StrConversion.__default.charToDigit();
  }
  public static dafny.DafnyMap<? extends java.lang.Byte, ? extends java.math.BigInteger> DIGITS()
  {
    return Std.JSON.ByteStrConversion.__default.charToDigit();
  }
  public static byte MINUS()
  {
    return ((byte) ('-'));
  }
  @Override
  public java.lang.String toString() {
    return "Std.JSON.Deserializer._default";
  }
}
