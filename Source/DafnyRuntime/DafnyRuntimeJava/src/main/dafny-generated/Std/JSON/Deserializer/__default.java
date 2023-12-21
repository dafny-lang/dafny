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
    java.math.BigInteger _495_hd = Std.JSON.Deserializer.Uint16StrConversion.__default.ToNat(str);
    return (_495_hd).shortValue();
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
          short _496_c = ((short)(java.lang.Object)((str).select(dafny.Helpers.toInt(((start).add(java.math.BigInteger.ONE))))));
          if ((_496_c) == (((short) ('u')))) {
            if ((java.math.BigInteger.valueOf((str).length())).compareTo((start).add(java.math.BigInteger.valueOf(6L))) <= 0) {
              return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Short>, Std.JSON.Errors.DeserializationError>create_Failure(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Errors.DeserializationError.create_EscapeAtEOS());
            } else {
              dafny.DafnySequence<? extends java.lang.Short> _497_code = (str).subsequence(dafny.Helpers.toInt(((start).add(java.math.BigInteger.valueOf(2L)))), dafny.Helpers.toInt(((start).add(java.math.BigInteger.valueOf(6L)))));
              if (((java.util.function.Function<dafny.DafnySequence<? extends java.lang.Short>, Boolean>)(_498_code) -> dafny.Helpers.Quantifier((_498_code).UniqueElements(), false, ((_exists_var_0_boxed0) -> {
                short _exists_var_0 = ((short)(java.lang.Object)(_exists_var_0_boxed0));
                if (true) {
                  short _499_c = (short)_exists_var_0;
                  return ((_498_code).contains(_499_c)) && (!(__default.HEX__TABLE__16()).<java.lang.Short>contains(_499_c));
                } else {
                  return false;
                }
              }))).apply(_497_code)) {
                return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Short>, Std.JSON.Errors.DeserializationError>create_Failure(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), __default.UnsupportedEscape16(_497_code));
              } else {
                short _500_hd = __default.ToNat16(_497_code);
                dafny.DafnySequence<? extends java.lang.Short> _in86 = str;
                java.math.BigInteger _in87 = (start).add(java.math.BigInteger.valueOf(6L));
                dafny.DafnySequence<? extends java.lang.Short> _in88 = dafny.DafnySequence.<java.lang.Short>concatenate(prefix, dafny.DafnySequence.<java.lang.Short> of(_500_hd));
                str = _in86;
                start = _in87;
                prefix = _in88;
                continue TAIL_CALL_START;
              }
            }
          } else {
            short _501_unescaped = (((_496_c) == ((short) 34)) ? ((short) 34) : ((((_496_c) == ((short) 92)) ? ((short) 92) : ((((_496_c) == ((short) 98)) ? ((short) 8) : ((((_496_c) == ((short) 102)) ? ((short) 12) : ((((_496_c) == ((short) 110)) ? ((short) 10) : ((((_496_c) == ((short) 114)) ? ((short) 13) : ((((_496_c) == ((short) 116)) ? ((short) 9) : ((short) 0))))))))))))));
            if ((dafny.Helpers.unsignedToBigInteger(_501_unescaped)).signum() == 0) {
              return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Short>, Std.JSON.Errors.DeserializationError>create_Failure(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), __default.UnsupportedEscape16((str).subsequence(dafny.Helpers.toInt((start)), dafny.Helpers.toInt(((start).add(java.math.BigInteger.valueOf(2L)))))));
            } else {
              dafny.DafnySequence<? extends java.lang.Short> _in89 = str;
              java.math.BigInteger _in90 = (start).add(java.math.BigInteger.valueOf(2L));
              dafny.DafnySequence<? extends java.lang.Short> _in91 = dafny.DafnySequence.<java.lang.Short>concatenate(prefix, dafny.DafnySequence.<java.lang.Short> of(_501_unescaped));
              str = _in89;
              start = _in90;
              prefix = _in91;
              continue TAIL_CALL_START;
            }
          }
        }
      } else {
        dafny.DafnySequence<? extends java.lang.Short> _in92 = str;
        java.math.BigInteger _in93 = (start).add(java.math.BigInteger.ONE);
        dafny.DafnySequence<? extends java.lang.Short> _in94 = dafny.DafnySequence.<java.lang.Short>concatenate(prefix, dafny.DafnySequence.<java.lang.Short> of(((short)(java.lang.Object)((str).select(dafny.Helpers.toInt((start)))))));
        str = _in92;
        start = _in93;
        prefix = _in94;
        continue TAIL_CALL_START;
      }
    }
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Errors.DeserializationError> String(Std.JSON.Grammar.jstring js) {
    Std.Wrappers.Result<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Errors.DeserializationError> _502_valueOrError0 = (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.FromUTF8Checked(((js).dtor_contents()).Bytes())).<Std.JSON.Errors.DeserializationError>ToResult(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Errors.DeserializationError.create_InvalidUnicode());
    if ((_502_valueOrError0).IsFailure(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor())) {
      return (_502_valueOrError0).<dafny.DafnySequence<? extends dafny.CodePoint>>PropagateFailure(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor(), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR));
    } else {
      dafny.DafnySequence<? extends dafny.CodePoint> _503_asUtf32 = (_502_valueOrError0).Extract(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor());
      Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Short>, Std.JSON.Errors.DeserializationError> _504_valueOrError1 = (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ToUTF16Checked(_503_asUtf32)).<Std.JSON.Errors.DeserializationError>ToResult(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Errors.DeserializationError.create_InvalidUnicode());
      if ((_504_valueOrError1).IsFailure(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor())) {
        return (_504_valueOrError1).<dafny.DafnySequence<? extends dafny.CodePoint>>PropagateFailure(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR));
      } else {
        dafny.DafnySequence<? extends java.lang.Short> _505_asUint16 = (_504_valueOrError1).Extract(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor());
        Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Short>, Std.JSON.Errors.DeserializationError> _506_valueOrError2 = __default.Unescape(_505_asUint16, java.math.BigInteger.ZERO, dafny.DafnySequence.<java.lang.Short> empty(Std.BoundedInts.uint16._typeDescriptor()));
        if ((_506_valueOrError2).IsFailure(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor())) {
          return (_506_valueOrError2).<dafny.DafnySequence<? extends dafny.CodePoint>>PropagateFailure(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR));
        } else {
          dafny.DafnySequence<? extends java.lang.Short> _507_unescaped = (_506_valueOrError2).Extract(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor());
          return (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.FromUTF16Checked(_507_unescaped)).<Std.JSON.Errors.DeserializationError>ToResult(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Errors.DeserializationError.create_InvalidUnicode());
        }
      }
    }
  }
  public static Std.Wrappers.Result<java.math.BigInteger, Std.JSON.Errors.DeserializationError> ToInt(Std.JSON.Utils.Views.Core.View__ sign, Std.JSON.Utils.Views.Core.View__ n)
  {
    java.math.BigInteger _508_n = Std.JSON.ByteStrConversion.__default.ToNat((n).Bytes());
    return Std.Wrappers.Result.<java.math.BigInteger, Std.JSON.Errors.DeserializationError>create_Success(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor(), (((sign).Char_q('-')) ? ((java.math.BigInteger.ZERO).subtract(_508_n)) : (_508_n)));
  }
  public static Std.Wrappers.Result<Std.JSON.Values.Decimal, Std.JSON.Errors.DeserializationError> Number(Std.JSON.Grammar.jnumber js) {
    Std.JSON.Grammar.jnumber _let_tmp_rhs17 = js;
    Std.JSON.Utils.Views.Core.View__ _509_minus = ((Std.JSON.Grammar.jnumber)_let_tmp_rhs17)._minus;
    Std.JSON.Utils.Views.Core.View__ _510_num = ((Std.JSON.Grammar.jnumber)_let_tmp_rhs17)._num;
    Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jfrac> _511_frac = ((Std.JSON.Grammar.jnumber)_let_tmp_rhs17)._frac;
    Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp> _512_exp = ((Std.JSON.Grammar.jnumber)_let_tmp_rhs17)._exp;
    Std.Wrappers.Result<java.math.BigInteger, Std.JSON.Errors.DeserializationError> _513_valueOrError0 = __default.ToInt(_509_minus, _510_num);
    if ((_513_valueOrError0).IsFailure(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor())) {
      return (_513_valueOrError0).<Std.JSON.Values.Decimal>PropagateFailure(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.Decimal._typeDescriptor());
    } else {
      java.math.BigInteger _514_n = (_513_valueOrError0).Extract(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor());
      Std.Wrappers.Result<java.math.BigInteger, Std.JSON.Errors.DeserializationError> _515_valueOrError1 = ((java.util.function.Function<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>, Std.Wrappers.Result<java.math.BigInteger, Std.JSON.Errors.DeserializationError>>)(_source17_boxed0) -> {
        Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp> _source17 = ((Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>)(java.lang.Object)(_source17_boxed0));
        if (_source17.is_Empty()) {
          return Std.Wrappers.Result.<java.math.BigInteger, Std.JSON.Errors.DeserializationError>create_Success(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor(), java.math.BigInteger.ZERO);
        } else {
          Std.JSON.Grammar.jexp _516___mcc_h0 = ((Std.JSON.Grammar.Maybe_NonEmpty<Std.JSON.Grammar.jexp>)_source17)._t;
          Std.JSON.Grammar.jexp _source18 = _516___mcc_h0;
          Std.JSON.Utils.Views.Core.View__ _517___mcc_h1 = ((Std.JSON.Grammar.jexp)_source18)._e;
          Std.JSON.Utils.Views.Core.View__ _518___mcc_h2 = ((Std.JSON.Grammar.jexp)_source18)._sign;
          Std.JSON.Utils.Views.Core.View__ _519___mcc_h3 = ((Std.JSON.Grammar.jexp)_source18)._num;
          Std.JSON.Utils.Views.Core.View__ _520_num = _519___mcc_h3;
          Std.JSON.Utils.Views.Core.View__ _521_sign = _518___mcc_h2;
          return __default.ToInt(_521_sign, _520_num);
        }
      }).apply(_512_exp);
      if ((_515_valueOrError1).IsFailure(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor())) {
        return (_515_valueOrError1).<Std.JSON.Values.Decimal>PropagateFailure(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.Decimal._typeDescriptor());
      } else {
        java.math.BigInteger _522_e10 = (_515_valueOrError1).Extract(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor());
        Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jfrac> _source19 = _511_frac;
        if (_source19.is_Empty()) {
          return Std.Wrappers.Result.<Std.JSON.Values.Decimal, Std.JSON.Errors.DeserializationError>create_Success(Std.JSON.Values.Decimal._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.Decimal.create(_514_n, _522_e10));
        } else {
          Std.JSON.Grammar.jfrac _523___mcc_h4 = ((Std.JSON.Grammar.Maybe_NonEmpty<Std.JSON.Grammar.jfrac>)_source19)._t;
          Std.JSON.Grammar.jfrac _source20 = _523___mcc_h4;
          Std.JSON.Utils.Views.Core.View__ _524___mcc_h5 = ((Std.JSON.Grammar.jfrac)_source20)._period;
          Std.JSON.Utils.Views.Core.View__ _525___mcc_h6 = ((Std.JSON.Grammar.jfrac)_source20)._num;
          Std.JSON.Utils.Views.Core.View__ _526_num = _525___mcc_h6;
          java.math.BigInteger _527_pow10 = dafny.Helpers.unsignedToBigInteger((_526_num).Length());
          Std.Wrappers.Result<java.math.BigInteger, Std.JSON.Errors.DeserializationError> _528_valueOrError2 = __default.ToInt(_509_minus, _526_num);
          if ((_528_valueOrError2).IsFailure(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor())) {
            return (_528_valueOrError2).<Std.JSON.Values.Decimal>PropagateFailure(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.Decimal._typeDescriptor());
          } else {
            java.math.BigInteger _529_frac = (_528_valueOrError2).Extract(dafny.TypeDescriptor.BIG_INTEGER, Std.JSON.Errors.DeserializationError._typeDescriptor());
            return Std.Wrappers.Result.<Std.JSON.Values.Decimal, Std.JSON.Errors.DeserializationError>create_Success(Std.JSON.Values.Decimal._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.Decimal.create(((_514_n).multiply(Std.Arithmetic.Power.__default.Pow(java.math.BigInteger.valueOf(10L), _527_pow10))).add(_529_frac), (_522_e10).subtract(_527_pow10)));
          }
        }
      }
    }
  }
  public static Std.Wrappers.Result<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>, Std.JSON.Errors.DeserializationError> KeyValue(Std.JSON.Grammar.jKeyValue js) {
    Std.Wrappers.Result<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Errors.DeserializationError> _530_valueOrError0 = __default.String((js).dtor_k());
    if ((_530_valueOrError0).IsFailure(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor())) {
      return (_530_valueOrError0).<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>>PropagateFailure(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor(), dafny.Tuple2.<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>_typeDescriptor(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Values.JSON._typeDescriptor()));
    } else {
      dafny.DafnySequence<? extends dafny.CodePoint> _531_k = (_530_valueOrError0).Extract(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor());
      Std.Wrappers.Result<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError> _532_valueOrError1 = __default.Value((js).dtor_v());
      if ((_532_valueOrError1).IsFailure(Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor())) {
        return (_532_valueOrError1).<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>>PropagateFailure(Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), dafny.Tuple2.<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>_typeDescriptor(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Values.JSON._typeDescriptor()));
      } else {
        Std.JSON.Values.JSON _533_v = (_532_valueOrError1).Extract(Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor());
        return Std.Wrappers.Result.<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>, Std.JSON.Errors.DeserializationError>create_Success(dafny.Tuple2.<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>_typeDescriptor(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Values.JSON._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), dafny.Tuple2.<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>create(_531_k, _533_v));
      }
    }
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>>, Std.JSON.Errors.DeserializationError> Object(Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> js) {
    return Std.Collections.Seq.__default.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>, dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>, Std.JSON.Errors.DeserializationError>MapWithResult(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jKeyValue._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor()), dafny.Tuple2.<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>_typeDescriptor(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Values.JSON._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), ((java.util.function.Function<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>, java.util.function.Function<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>, Std.Wrappers.Result<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>, Std.JSON.Errors.DeserializationError>>>)(_534_js) -> ((java.util.function.Function<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>, Std.Wrappers.Result<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>, Std.JSON.Errors.DeserializationError>>)(_535_d_boxed0) -> {
      Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__> _535_d = ((Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>)(java.lang.Object)(_535_d_boxed0));
      return __default.KeyValue((_535_d).dtor_t());
    })).apply(js), (js).dtor_data());
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends Std.JSON.Values.JSON>, Std.JSON.Errors.DeserializationError> Array(Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> js) {
    return Std.Collections.Seq.__default.<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>, Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError>MapWithResult(Std.JSON.Grammar.Suffixed.<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.jcomma._typeDescriptor()), Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), ((java.util.function.Function<Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__>, java.util.function.Function<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>, Std.Wrappers.Result<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError>>>)(_536_js) -> ((java.util.function.Function<Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>, Std.Wrappers.Result<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError>>)(_537_d_boxed0) -> {
      Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__> _537_d = ((Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>)(java.lang.Object)(_537_d_boxed0));
      return __default.Value((_537_d).dtor_t());
    })).apply(js), (js).dtor_data());
  }
  public static Std.Wrappers.Result<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError> Value(Std.JSON.Grammar.Value js) {
    Std.JSON.Grammar.Value _source21 = js;
    if (_source21.is_Null()) {
      Std.JSON.Utils.Views.Core.View__ _538___mcc_h0 = ((Std.JSON.Grammar.Value_Null)_source21)._n;
      return Std.Wrappers.Result.<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError>create_Success(Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON.create_Null());
    } else if (_source21.is_Bool()) {
      Std.JSON.Utils.Views.Core.View__ _539___mcc_h1 = ((Std.JSON.Grammar.Value_Bool)_source21)._b;
      Std.JSON.Utils.Views.Core.View__ _540_b = _539___mcc_h1;
      return Std.Wrappers.Result.<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError>create_Success(Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON.create_Bool(__default.Bool(_540_b)));
    } else if (_source21.is_String()) {
      Std.JSON.Grammar.jstring _541___mcc_h2 = ((Std.JSON.Grammar.Value_String)_source21)._str;
      Std.JSON.Grammar.jstring _542_str = _541___mcc_h2;
      Std.Wrappers.Result<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Errors.DeserializationError> _543_valueOrError0 = __default.String(_542_str);
      if ((_543_valueOrError0).IsFailure(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor())) {
        return (_543_valueOrError0).<Std.JSON.Values.JSON>PropagateFailure(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON._typeDescriptor());
      } else {
        dafny.DafnySequence<? extends dafny.CodePoint> _544_s = (_543_valueOrError0).Extract(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.DeserializationError._typeDescriptor());
        return Std.Wrappers.Result.<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError>create_Success(Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON.create_String(_544_s));
      }
    } else if (_source21.is_Number()) {
      Std.JSON.Grammar.jnumber _545___mcc_h3 = ((Std.JSON.Grammar.Value_Number)_source21)._num;
      Std.JSON.Grammar.jnumber _546_dec = _545___mcc_h3;
      Std.Wrappers.Result<Std.JSON.Values.Decimal, Std.JSON.Errors.DeserializationError> _547_valueOrError1 = __default.Number(_546_dec);
      if ((_547_valueOrError1).IsFailure(Std.JSON.Values.Decimal._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor())) {
        return (_547_valueOrError1).<Std.JSON.Values.JSON>PropagateFailure(Std.JSON.Values.Decimal._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON._typeDescriptor());
      } else {
        Std.JSON.Values.Decimal _548_n = (_547_valueOrError1).Extract(Std.JSON.Values.Decimal._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor());
        return Std.Wrappers.Result.<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError>create_Success(Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON.create_Number(_548_n));
      }
    } else if (_source21.is_Object()) {
      Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> _549___mcc_h4 = ((Std.JSON.Grammar.Value_Object)_source21)._obj;
      Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> _550_obj = _549___mcc_h4;
      Std.Wrappers.Result<dafny.DafnySequence<? extends dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>>, Std.JSON.Errors.DeserializationError> _551_valueOrError2 = __default.Object(_550_obj);
      if ((_551_valueOrError2).IsFailure(dafny.DafnySequence.<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>>_typeDescriptor(dafny.Tuple2.<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>_typeDescriptor(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Values.JSON._typeDescriptor())), Std.JSON.Errors.DeserializationError._typeDescriptor())) {
        return (_551_valueOrError2).<Std.JSON.Values.JSON>PropagateFailure(dafny.DafnySequence.<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>>_typeDescriptor(dafny.Tuple2.<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>_typeDescriptor(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Values.JSON._typeDescriptor())), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON._typeDescriptor());
      } else {
        dafny.DafnySequence<? extends dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>> _552_o = (_551_valueOrError2).Extract(dafny.DafnySequence.<dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>>_typeDescriptor(dafny.Tuple2.<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>_typeDescriptor(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Values.JSON._typeDescriptor())), Std.JSON.Errors.DeserializationError._typeDescriptor());
        return Std.Wrappers.Result.<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError>create_Success(Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON.create_Object(_552_o));
      }
    } else {
      Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> _553___mcc_h5 = ((Std.JSON.Grammar.Value_Array)_source21)._arr;
      Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> _554_arr = _553___mcc_h5;
      Std.Wrappers.Result<dafny.DafnySequence<? extends Std.JSON.Values.JSON>, Std.JSON.Errors.DeserializationError> _555_valueOrError3 = __default.Array(_554_arr);
      if ((_555_valueOrError3).IsFailure(dafny.DafnySequence.<Std.JSON.Values.JSON>_typeDescriptor(Std.JSON.Values.JSON._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor())) {
        return (_555_valueOrError3).<Std.JSON.Values.JSON>PropagateFailure(dafny.DafnySequence.<Std.JSON.Values.JSON>_typeDescriptor(Std.JSON.Values.JSON._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON._typeDescriptor());
      } else {
        dafny.DafnySequence<? extends Std.JSON.Values.JSON> _556_a = (_555_valueOrError3).Extract(dafny.DafnySequence.<Std.JSON.Values.JSON>_typeDescriptor(Std.JSON.Values.JSON._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor());
        return Std.Wrappers.Result.<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError>create_Success(Std.JSON.Values.JSON._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON.create_Array(_556_a));
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
