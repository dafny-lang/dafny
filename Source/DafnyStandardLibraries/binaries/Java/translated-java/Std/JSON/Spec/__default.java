// Class __default
// Dafny class __default compiled into Java
package Std.JSON.Spec;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static dafny.DafnySequence<? extends java.lang.Short> EscapeUnicode(short c) {
    dafny.DafnySequence<? extends dafny.CodePoint> _318_sStr = Std.Strings.HexConversion.__default.OfNat(dafny.Helpers.unsignedToBigInteger(c));
    dafny.DafnySequence<? extends java.lang.Short> _319_s = Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(_318_sStr);
    return dafny.DafnySequence.<java.lang.Short>concatenate(_319_s, dafny.DafnySequence.Create(Std.BoundedInts.uint16._typeDescriptor(), (java.math.BigInteger.valueOf(4L)).subtract(java.math.BigInteger.valueOf((_319_s).length())), ((java.util.function.Function<java.math.BigInteger, java.lang.Short>)(_320___v8_boxed0) -> {
      java.math.BigInteger _320___v8 = ((java.math.BigInteger)(java.lang.Object)(_320___v8_boxed0));
      return ((short) (' '));
    })));
  }
  public static dafny.DafnySequence<? extends java.lang.Short> Escape(dafny.DafnySequence<? extends java.lang.Short> str, java.math.BigInteger start)
  {
    dafny.DafnySequence<? extends java.lang.Short> _321___accumulator = dafny.DafnySequence.<java.lang.Short> empty(Std.BoundedInts.uint16._typeDescriptor());
    TAIL_CALL_START: while (true) {
      dafny.DafnySequence<? extends java.lang.Short> _pat_let_tv0 = str;
      java.math.BigInteger _pat_let_tv1 = start;
      if ((start).compareTo(java.math.BigInteger.valueOf((str).length())) >= 0) {
        return dafny.DafnySequence.<java.lang.Short>concatenate(_321___accumulator, dafny.DafnySequence.<java.lang.Short> empty(Std.BoundedInts.uint16._typeDescriptor()));
      } else {
        _321___accumulator = dafny.DafnySequence.<java.lang.Short>concatenate(_321___accumulator, (((((short)(java.lang.Object)((str).select(dafny.Helpers.toInt((start)))))) == ((short) 34)) ? (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(dafny.DafnySequence.asUnicodeString("\\\""))) : ((((((short)(java.lang.Object)((str).select(dafny.Helpers.toInt((start)))))) == ((short) 92)) ? (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(dafny.DafnySequence.asUnicodeString("\\\\"))) : ((((((short)(java.lang.Object)((str).select(dafny.Helpers.toInt((start)))))) == ((short) 8)) ? (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(dafny.DafnySequence.asUnicodeString("\\b"))) : ((((((short)(java.lang.Object)((str).select(dafny.Helpers.toInt((start)))))) == ((short) 12)) ? (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(dafny.DafnySequence.asUnicodeString("\\f"))) : ((((((short)(java.lang.Object)((str).select(dafny.Helpers.toInt((start)))))) == ((short) 10)) ? (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(dafny.DafnySequence.asUnicodeString("\\n"))) : ((((((short)(java.lang.Object)((str).select(dafny.Helpers.toInt((start)))))) == ((short) 13)) ? (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(dafny.DafnySequence.asUnicodeString("\\r"))) : ((((((short)(java.lang.Object)((str).select(dafny.Helpers.toInt((start)))))) == ((short) 9)) ? (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(dafny.DafnySequence.asUnicodeString("\\t"))) : (((dafny.DafnySequence<? extends java.lang.Short>)(java.lang.Object)(dafny.Helpers.<java.lang.Short, dafny.DafnySequence<? extends java.lang.Short>>Let(((short)(java.lang.Object)((str).select(dafny.Helpers.toInt((start))))), boxed0 -> {
          short _pat_let1_0 = ((short)(java.lang.Object)(boxed0));
          return ((dafny.DafnySequence<? extends java.lang.Short>)(java.lang.Object)(dafny.Helpers.<java.lang.Short, dafny.DafnySequence<? extends java.lang.Short>>Let(_pat_let1_0, boxed1 -> {
            short _322_c = ((short)(java.lang.Object)(boxed1));
            return ((java.lang.Integer.compareUnsigned(_322_c, (short) 31) < 0) ? (dafny.DafnySequence.<java.lang.Short>concatenate(Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(dafny.DafnySequence.asUnicodeString("\\u")), __default.EscapeUnicode(_322_c))) : (dafny.DafnySequence.<java.lang.Short> of(((short)(java.lang.Object)((_pat_let_tv0).select(dafny.Helpers.toInt((_pat_let_tv1))))))));
          }
          )));
        }
        ))))))))))))))))));
        dafny.DafnySequence<? extends java.lang.Short> _in61 = str;
        java.math.BigInteger _in62 = (start).add(java.math.BigInteger.ONE);
        str = _in61;
        start = _in62;
        continue TAIL_CALL_START;
      }
    }
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError> EscapeToUTF8(dafny.DafnySequence<? extends dafny.CodePoint> str, java.math.BigInteger start)
  {
    Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Short>, Std.JSON.Errors.SerializationError> _323_valueOrError0 = (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ToUTF16Checked(str)).<Std.JSON.Errors.SerializationError>ToResult(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Errors.SerializationError.create_InvalidUnicode());
    if ((_323_valueOrError0).IsFailure(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor())) {
      return (_323_valueOrError0).<dafny.DafnySequence<? extends java.lang.Byte>>PropagateFailure(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()));
    } else {
      dafny.DafnySequence<? extends java.lang.Short> _324_utf16 = (_323_valueOrError0).Extract(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor());
      dafny.DafnySequence<? extends java.lang.Short> _325_escaped = __default.Escape(_324_utf16, java.math.BigInteger.ZERO);
      Std.Wrappers.Result<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Errors.SerializationError> _326_valueOrError1 = (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.FromUTF16Checked(_325_escaped)).<Std.JSON.Errors.SerializationError>ToResult(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Errors.SerializationError.create_InvalidUnicode());
      if ((_326_valueOrError1).IsFailure(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.SerializationError._typeDescriptor())) {
        return (_326_valueOrError1).<dafny.DafnySequence<? extends java.lang.Byte>>PropagateFailure(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.SerializationError._typeDescriptor(), dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()));
      } else {
        dafny.DafnySequence<? extends dafny.CodePoint> _327_utf32 = (_326_valueOrError1).Extract(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Errors.SerializationError._typeDescriptor());
        return (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ToUTF8Checked(_327_utf32)).<Std.JSON.Errors.SerializationError>ToResult(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Errors.SerializationError.create_InvalidUnicode());
      }
    }
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError> String(dafny.DafnySequence<? extends dafny.CodePoint> str) {
    Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError> _328_valueOrError0 = __default.EscapeToUTF8(str, java.math.BigInteger.ZERO);
    if ((_328_valueOrError0).IsFailure(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor())) {
      return (_328_valueOrError0).<dafny.DafnySequence<? extends java.lang.Byte>>PropagateFailure(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()));
    } else {
      dafny.DafnySequence<? extends java.lang.Byte> _329_inBytes = (_328_valueOrError0).Extract(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor());
      return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError>create_Success(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(dafny.DafnySequence.asUnicodeString("\"")), _329_inBytes), Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(dafny.DafnySequence.asUnicodeString("\""))));
    }
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> IntToBytes(java.math.BigInteger n) {
    dafny.DafnySequence<? extends dafny.CodePoint> _330_s = Std.Strings.__default.OfInt(n);
    return Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_330_s);
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError> Number(Std.JSON.Values.Decimal dec) {
    return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError>create_Success(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), dafny.DafnySequence.<java.lang.Byte>concatenate(__default.IntToBytes((dec).dtor_n()), ((((dec).dtor_e10()).signum() == 0) ? (dafny.DafnySequence.<java.lang.Byte> empty(Std.BoundedInts.uint8._typeDescriptor())) : (dafny.DafnySequence.<java.lang.Byte>concatenate(Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(dafny.DafnySequence.asUnicodeString("e")), __default.IntToBytes((dec).dtor_e10()))))));
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError> KeyValue(dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON> kv) {
    Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError> _331_valueOrError0 = __default.String((kv).dtor__0());
    if ((_331_valueOrError0).IsFailure(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor())) {
      return (_331_valueOrError0).<dafny.DafnySequence<? extends java.lang.Byte>>PropagateFailure(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()));
    } else {
      dafny.DafnySequence<? extends java.lang.Byte> _332_key = (_331_valueOrError0).Extract(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor());
      Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError> _333_valueOrError1 = __default.JSON((kv).dtor__1());
      if ((_333_valueOrError1).IsFailure(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor())) {
        return (_333_valueOrError1).<dafny.DafnySequence<? extends java.lang.Byte>>PropagateFailure(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()));
      } else {
        dafny.DafnySequence<? extends java.lang.Byte> _334_value = (_333_valueOrError1).Extract(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor());
        return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError>create_Success(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(_332_key, Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(dafny.DafnySequence.asUnicodeString(":"))), _334_value));
      }
    }
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError> Join(dafny.DafnySequence<? extends java.lang.Byte> sep, dafny.DafnySequence<? extends Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError>> items)
  {
    if ((java.math.BigInteger.valueOf((items).length())).signum() == 0) {
      return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError>create_Success(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), dafny.DafnySequence.<java.lang.Byte> empty(Std.BoundedInts.uint8._typeDescriptor()));
    } else {
      Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError> _335_valueOrError0 = ((Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError>)(java.lang.Object)((items).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
      if ((_335_valueOrError0).IsFailure(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor())) {
        return (_335_valueOrError0).<dafny.DafnySequence<? extends java.lang.Byte>>PropagateFailure(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()));
      } else {
        dafny.DafnySequence<? extends java.lang.Byte> _336_first = (_335_valueOrError0).Extract(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor());
        if (java.util.Objects.equals(java.math.BigInteger.valueOf((items).length()), java.math.BigInteger.ONE)) {
          return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError>create_Success(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), _336_first);
        } else {
          Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError> _337_valueOrError1 = __default.Join(sep, (items).drop(java.math.BigInteger.ONE));
          if ((_337_valueOrError1).IsFailure(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor())) {
            return (_337_valueOrError1).<dafny.DafnySequence<? extends java.lang.Byte>>PropagateFailure(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()));
          } else {
            dafny.DafnySequence<? extends java.lang.Byte> _338_rest = (_337_valueOrError1).Extract(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor());
            return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError>create_Success(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(_336_first, sep), _338_rest));
          }
        }
      }
    }
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError> Object(dafny.DafnySequence<? extends dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>> obj) {
    Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError> _339_valueOrError0 = __default.Join(Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(dafny.DafnySequence.asUnicodeString(",")), dafny.DafnySequence.Create(Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError>_typeDescriptor(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor()), java.math.BigInteger.valueOf((obj).length()), ((java.util.function.Function<dafny.DafnySequence<? extends dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>>, java.util.function.Function<java.math.BigInteger, Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError>>>)(_340_obj) -> ((java.util.function.Function<java.math.BigInteger, Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError>>)(_341_i_boxed0) -> {
      java.math.BigInteger _341_i = ((java.math.BigInteger)(java.lang.Object)(_341_i_boxed0));
      return __default.KeyValue(((dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>)(java.lang.Object)((_340_obj).select(dafny.Helpers.toInt((_341_i))))));
    })).apply(obj)));
    if ((_339_valueOrError0).IsFailure(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor())) {
      return (_339_valueOrError0).<dafny.DafnySequence<? extends java.lang.Byte>>PropagateFailure(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()));
    } else {
      dafny.DafnySequence<? extends java.lang.Byte> _342_middle = (_339_valueOrError0).Extract(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor());
      return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError>create_Success(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(dafny.DafnySequence.asUnicodeString("{")), _342_middle), Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(dafny.DafnySequence.asUnicodeString("}"))));
    }
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError> Array(dafny.DafnySequence<? extends Std.JSON.Values.JSON> arr) {
    Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError> _343_valueOrError0 = __default.Join(Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(dafny.DafnySequence.asUnicodeString(",")), dafny.DafnySequence.Create(Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError>_typeDescriptor(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor()), java.math.BigInteger.valueOf((arr).length()), ((java.util.function.Function<dafny.DafnySequence<? extends Std.JSON.Values.JSON>, java.util.function.Function<java.math.BigInteger, Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError>>>)(_344_arr) -> ((java.util.function.Function<java.math.BigInteger, Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError>>)(_345_i_boxed0) -> {
      java.math.BigInteger _345_i = ((java.math.BigInteger)(java.lang.Object)(_345_i_boxed0));
      return __default.JSON(((Std.JSON.Values.JSON)(java.lang.Object)((_344_arr).select(dafny.Helpers.toInt((_345_i))))));
    })).apply(arr)));
    if ((_343_valueOrError0).IsFailure(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor())) {
      return (_343_valueOrError0).<dafny.DafnySequence<? extends java.lang.Byte>>PropagateFailure(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()));
    } else {
      dafny.DafnySequence<? extends java.lang.Byte> _346_middle = (_343_valueOrError0).Extract(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor());
      return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError>create_Success(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(dafny.DafnySequence.asUnicodeString("[")), _346_middle), Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(dafny.DafnySequence.asUnicodeString("]"))));
    }
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError> JSON(Std.JSON.Values.JSON js) {
    Std.JSON.Values.JSON _source12 = js;
    if (_source12.is_Null()) {
      return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError>create_Success(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(dafny.DafnySequence.asUnicodeString("null")));
    } else if (_source12.is_Bool()) {
      boolean _347___mcc_h0 = ((Std.JSON.Values.JSON_Bool)_source12)._b;
      boolean _348_b = _347___mcc_h0;
      return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError>create_Success(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), ((_348_b) ? (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(dafny.DafnySequence.asUnicodeString("true"))) : (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(dafny.DafnySequence.asUnicodeString("false")))));
    } else if (_source12.is_String()) {
      dafny.DafnySequence<? extends dafny.CodePoint> _349___mcc_h1 = ((Std.JSON.Values.JSON_String)_source12)._str;
      dafny.DafnySequence<? extends dafny.CodePoint> _350_str = _349___mcc_h1;
      return __default.String(_350_str);
    } else if (_source12.is_Number()) {
      Std.JSON.Values.Decimal _351___mcc_h2 = ((Std.JSON.Values.JSON_Number)_source12)._num;
      Std.JSON.Values.Decimal _352_dec = _351___mcc_h2;
      return __default.Number(_352_dec);
    } else if (_source12.is_Object()) {
      dafny.DafnySequence<? extends dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>> _353___mcc_h3 = ((Std.JSON.Values.JSON_Object)_source12)._obj;
      dafny.DafnySequence<? extends dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, Std.JSON.Values.JSON>> _354_obj = _353___mcc_h3;
      return __default.Object(_354_obj);
    } else {
      dafny.DafnySequence<? extends Std.JSON.Values.JSON> _355___mcc_h4 = ((Std.JSON.Values.JSON_Array)_source12)._arr;
      dafny.DafnySequence<? extends Std.JSON.Values.JSON> _356_arr = _355___mcc_h4;
      return __default.Array(_356_arr);
    }
  }
  @Override
  public java.lang.String toString() {
    return "Std.JSON.Spec._default";
  }
}
