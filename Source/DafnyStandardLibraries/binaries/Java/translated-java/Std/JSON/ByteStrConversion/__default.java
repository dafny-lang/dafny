// Class __default
// Dafny class __default compiled into Java
package Std.JSON.ByteStrConversion;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static java.math.BigInteger BASE() {
    return __default.base();
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> OfDigits(dafny.DafnySequence<? extends java.math.BigInteger> digits) {
    dafny.DafnySequence<? extends java.lang.Byte> _407___accumulator = dafny.DafnySequence.<java.lang.Byte> empty(Std.BoundedInts.uint8._typeDescriptor());
    TAIL_CALL_START: while (true) {
      if ((digits).equals(dafny.DafnySequence.<java.math.BigInteger> empty(dafny.TypeDescriptor.BIG_INTEGER))) {
        return dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte> empty(Std.BoundedInts.uint8._typeDescriptor()), _407___accumulator);
      } else {
        _407___accumulator = dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte> of(((byte)(java.lang.Object)((__default.chars()).select(dafny.Helpers.toInt((((java.math.BigInteger)(java.lang.Object)((digits).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))))))))), _407___accumulator);
        dafny.DafnySequence<? extends java.math.BigInteger> _in72 = (digits).drop(java.math.BigInteger.ONE);
        digits = _in72;
        continue TAIL_CALL_START;
      }
    }
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> OfNat(java.math.BigInteger n) {
    if ((n).signum() == 0) {
      return dafny.DafnySequence.<java.lang.Byte> of(((byte)(java.lang.Object)((__default.chars()).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))));
    } else {
      return __default.OfDigits(__default.FromNat(n));
    }
  }
  public static boolean OfNumberStr(dafny.DafnySequence<? extends java.lang.Byte> str, byte minus)
  {
    return !(!(str).equals(dafny.DafnySequence.<java.lang.Byte> empty(Std.BoundedInts.uint8._typeDescriptor()))) || ((((((byte)(java.lang.Object)((str).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))))) == (minus)) || ((__default.chars()).contains(((byte)(java.lang.Object)((str).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))))))) && (((java.util.function.Function<dafny.DafnySequence<? extends java.lang.Byte>, Boolean>)(_408_str) -> dafny.Helpers.Quantifier(((_408_str).drop(java.math.BigInteger.ONE)).UniqueElements(), true, ((_forall_var_5_boxed0) -> {
      byte _forall_var_5 = ((byte)(java.lang.Object)(_forall_var_5_boxed0));
      if (true) {
        byte _409_c = (byte)_forall_var_5;
        return !(((_408_str).drop(java.math.BigInteger.ONE)).contains(_409_c)) || ((__default.chars()).contains(_409_c));
      } else {
        return true;
      }
    }))).apply(str)));
  }
  public static boolean ToNumberStr(dafny.DafnySequence<? extends java.lang.Byte> str, byte minus)
  {
    return !(!(str).equals(dafny.DafnySequence.<java.lang.Byte> empty(Std.BoundedInts.uint8._typeDescriptor()))) || ((((((byte)(java.lang.Object)((str).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))))) == (minus)) || ((__default.charToDigit()).<java.lang.Byte>contains(((byte)(java.lang.Object)((str).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))))))) && (((java.util.function.Function<dafny.DafnySequence<? extends java.lang.Byte>, Boolean>)(_410_str) -> dafny.Helpers.Quantifier(((_410_str).drop(java.math.BigInteger.ONE)).UniqueElements(), true, ((_forall_var_6_boxed0) -> {
      byte _forall_var_6 = ((byte)(java.lang.Object)(_forall_var_6_boxed0));
      if (true) {
        byte _411_c = (byte)_forall_var_6;
        return !(((_410_str).drop(java.math.BigInteger.ONE)).contains(_411_c)) || ((__default.charToDigit()).<java.lang.Byte>contains(_411_c));
      } else {
        return true;
      }
    }))).apply(str)));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> OfInt(java.math.BigInteger n, byte minus)
  {
    if ((n).signum() != -1) {
      return __default.OfNat(n);
    } else {
      return dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte> of(minus), __default.OfNat((java.math.BigInteger.ZERO).subtract(n)));
    }
  }
  public static java.math.BigInteger ToNat(dafny.DafnySequence<? extends java.lang.Byte> str) {
    if ((str).equals(dafny.DafnySequence.<java.lang.Byte> empty(Std.BoundedInts.uint8._typeDescriptor()))) {
      return java.math.BigInteger.ZERO;
    } else {
      return ((__default.ToNat((str).take((java.math.BigInteger.valueOf((str).length())).subtract(java.math.BigInteger.ONE)))).multiply(__default.base())).add(((java.math.BigInteger)(java.lang.Object)((__default.charToDigit()).get(((byte)(java.lang.Object)((str).select(dafny.Helpers.toInt(((java.math.BigInteger.valueOf((str).length())).subtract(java.math.BigInteger.ONE))))))))));
    }
  }
  public static java.math.BigInteger ToInt(dafny.DafnySequence<? extends java.lang.Byte> str, byte minus)
  {
    if ((dafny.DafnySequence.<java.lang.Byte> of(minus)).isPrefixOf(str)) {
      return (java.math.BigInteger.ZERO).subtract(__default.ToNat((str).drop(java.math.BigInteger.ONE)));
    } else {
      return __default.ToNat(str);
    }
  }
  public static java.math.BigInteger ToNatRight(dafny.DafnySequence<? extends java.math.BigInteger> xs) {
    if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
      return java.math.BigInteger.ZERO;
    } else {
      return ((__default.ToNatRight(Std.Collections.Seq.__default.<java.math.BigInteger>DropFirst(digit._typeDescriptor(), xs))).multiply(__default.BASE())).add(Std.Collections.Seq.__default.<java.math.BigInteger>First(digit._typeDescriptor(), xs));
    }
  }
  public static java.math.BigInteger ToNatLeft(dafny.DafnySequence<? extends java.math.BigInteger> xs) {
    java.math.BigInteger _412___accumulator = java.math.BigInteger.ZERO;
    TAIL_CALL_START: while (true) {
      if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
        return (java.math.BigInteger.ZERO).add(_412___accumulator);
      } else {
        _412___accumulator = ((Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, xs)).multiply(Std.Arithmetic.Power.__default.Pow(__default.BASE(), (java.math.BigInteger.valueOf((xs).length())).subtract(java.math.BigInteger.ONE)))).add(_412___accumulator);
        dafny.DafnySequence<? extends java.math.BigInteger> _in73 = Std.Collections.Seq.__default.<java.math.BigInteger>DropLast(digit._typeDescriptor(), xs);
        xs = _in73;
        continue TAIL_CALL_START;
      }
    }
  }
  public static dafny.DafnySequence<? extends java.math.BigInteger> FromNat(java.math.BigInteger n) {
    dafny.DafnySequence<? extends java.math.BigInteger> _413___accumulator = dafny.DafnySequence.<java.math.BigInteger> empty(digit._typeDescriptor());
    TAIL_CALL_START: while (true) {
      if ((n).signum() == 0) {
        return dafny.DafnySequence.<java.math.BigInteger>concatenate(_413___accumulator, dafny.DafnySequence.<java.math.BigInteger> empty(dafny.TypeDescriptor.BIG_INTEGER));
      } else {
        _413___accumulator = dafny.DafnySequence.<java.math.BigInteger>concatenate(_413___accumulator, dafny.DafnySequence.<java.math.BigInteger> of(dafny.TypeDescriptor.BIG_INTEGER, dafny.DafnyEuclidean.EuclideanModulus(n, __default.BASE())));
        java.math.BigInteger _in74 = dafny.DafnyEuclidean.EuclideanDivision(n, __default.BASE());
        n = _in74;
        continue TAIL_CALL_START;
      }
    }
  }
  public static dafny.DafnySequence<? extends java.math.BigInteger> SeqExtend(dafny.DafnySequence<? extends java.math.BigInteger> xs, java.math.BigInteger n)
  {
    TAIL_CALL_START: while (true) {
      if ((java.math.BigInteger.valueOf((xs).length())).compareTo(n) >= 0) {
        return xs;
      } else {
        dafny.DafnySequence<? extends java.math.BigInteger> _in75 = dafny.DafnySequence.<java.math.BigInteger>concatenate(xs, dafny.DafnySequence.<java.math.BigInteger> of(digit._typeDescriptor(), java.math.BigInteger.ZERO));
        java.math.BigInteger _in76 = n;
        xs = _in75;
        n = _in76;
        continue TAIL_CALL_START;
      }
    }
  }
  public static dafny.DafnySequence<? extends java.math.BigInteger> SeqExtendMultiple(dafny.DafnySequence<? extends java.math.BigInteger> xs, java.math.BigInteger n)
  {
    java.math.BigInteger _414_newLen = ((java.math.BigInteger.valueOf((xs).length())).add(n)).subtract(dafny.DafnyEuclidean.EuclideanModulus(java.math.BigInteger.valueOf((xs).length()), n));
    return __default.SeqExtend(xs, _414_newLen);
  }
  public static dafny.DafnySequence<? extends java.math.BigInteger> FromNatWithLen(java.math.BigInteger n, java.math.BigInteger len)
  {
    return __default.SeqExtend(__default.FromNat(n), len);
  }
  public static dafny.DafnySequence<? extends java.math.BigInteger> SeqZero(java.math.BigInteger len) {
    dafny.DafnySequence<? extends java.math.BigInteger> _415_xs = __default.FromNatWithLen(java.math.BigInteger.ZERO, len);
    return _415_xs;
  }
  public static dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger> SeqAdd(dafny.DafnySequence<? extends java.math.BigInteger> xs, dafny.DafnySequence<? extends java.math.BigInteger> ys)
  {
    if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
      return dafny.Tuple2.<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>create(dafny.DafnySequence.<java.math.BigInteger> empty(dafny.TypeDescriptor.BIG_INTEGER), java.math.BigInteger.ZERO);
    } else {
      dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger> _let_tmp_rhs9 = __default.SeqAdd(Std.Collections.Seq.__default.<java.math.BigInteger>DropLast(digit._typeDescriptor(), xs), Std.Collections.Seq.__default.<java.math.BigInteger>DropLast(digit._typeDescriptor(), ys));
      dafny.DafnySequence<? extends java.math.BigInteger> _416_zs_k = ((dafny.DafnySequence<? extends java.math.BigInteger>)(java.lang.Object)(((dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>)_let_tmp_rhs9).dtor__0()));
      java.math.BigInteger _417_cin = ((java.math.BigInteger)(java.lang.Object)(((dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>)_let_tmp_rhs9).dtor__1()));
      java.math.BigInteger _418_sum = ((Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, xs)).add(Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, ys))).add(_417_cin);
      dafny.Tuple2<java.math.BigInteger, java.math.BigInteger> _let_tmp_rhs10 = (((_418_sum).compareTo(__default.BASE()) < 0) ? (dafny.Tuple2.<java.math.BigInteger, java.math.BigInteger>create(_418_sum, java.math.BigInteger.ZERO)) : (dafny.Tuple2.<java.math.BigInteger, java.math.BigInteger>create((_418_sum).subtract(__default.BASE()), java.math.BigInteger.ONE)));
      java.math.BigInteger _419_sum__out = ((java.math.BigInteger)(java.lang.Object)(((dafny.Tuple2<java.math.BigInteger, java.math.BigInteger>)_let_tmp_rhs10).dtor__0()));
      java.math.BigInteger _420_cout = ((java.math.BigInteger)(java.lang.Object)(((dafny.Tuple2<java.math.BigInteger, java.math.BigInteger>)_let_tmp_rhs10).dtor__1()));
      return dafny.Tuple2.<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>create(dafny.DafnySequence.<java.math.BigInteger>concatenate(_416_zs_k, dafny.DafnySequence.<java.math.BigInteger> of(dafny.TypeDescriptor.BIG_INTEGER, _419_sum__out)), _420_cout);
    }
  }
  public static dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger> SeqSub(dafny.DafnySequence<? extends java.math.BigInteger> xs, dafny.DafnySequence<? extends java.math.BigInteger> ys)
  {
    if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
      return dafny.Tuple2.<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>create(dafny.DafnySequence.<java.math.BigInteger> empty(dafny.TypeDescriptor.BIG_INTEGER), java.math.BigInteger.ZERO);
    } else {
      dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger> _let_tmp_rhs11 = __default.SeqSub(Std.Collections.Seq.__default.<java.math.BigInteger>DropLast(digit._typeDescriptor(), xs), Std.Collections.Seq.__default.<java.math.BigInteger>DropLast(digit._typeDescriptor(), ys));
      dafny.DafnySequence<? extends java.math.BigInteger> _421_zs = ((dafny.DafnySequence<? extends java.math.BigInteger>)(java.lang.Object)(((dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>)_let_tmp_rhs11).dtor__0()));
      java.math.BigInteger _422_cin = ((java.math.BigInteger)(java.lang.Object)(((dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>)_let_tmp_rhs11).dtor__1()));
      dafny.Tuple2<java.math.BigInteger, java.math.BigInteger> _let_tmp_rhs12 = (((Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, xs)).compareTo((Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, ys)).add(_422_cin)) >= 0) ? (dafny.Tuple2.<java.math.BigInteger, java.math.BigInteger>create(((Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, xs)).subtract(Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, ys))).subtract(_422_cin), java.math.BigInteger.ZERO)) : (dafny.Tuple2.<java.math.BigInteger, java.math.BigInteger>create((((__default.BASE()).add(Std.Collections.Seq.__default.<java.math.BigInteger>Last(digit._typeDescriptor(), xs))).subtract(Std.Collections.Seq.__default.<java.math.BigInteger>Last(digit._typeDescriptor(), ys))).subtract(_422_cin), java.math.BigInteger.ONE)));
      java.math.BigInteger _423_diff__out = ((java.math.BigInteger)(java.lang.Object)(((dafny.Tuple2<java.math.BigInteger, java.math.BigInteger>)_let_tmp_rhs12).dtor__0()));
      java.math.BigInteger _424_cout = ((java.math.BigInteger)(java.lang.Object)(((dafny.Tuple2<java.math.BigInteger, java.math.BigInteger>)_let_tmp_rhs12).dtor__1()));
      return dafny.Tuple2.<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>create(dafny.DafnySequence.<java.math.BigInteger>concatenate(_421_zs, dafny.DafnySequence.<java.math.BigInteger> of(dafny.TypeDescriptor.BIG_INTEGER, _423_diff__out)), _424_cout);
    }
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> chars()
  {
    return dafny.DafnySequence.<java.lang.Byte> of(((byte) ('0')), ((byte) ('1')), ((byte) ('2')), ((byte) ('3')), ((byte) ('4')), ((byte) ('5')), ((byte) ('6')), ((byte) ('7')), ((byte) ('8')), ((byte) ('9')));
  }
  public static java.math.BigInteger base()
  {
    return java.math.BigInteger.valueOf((__default.chars()).length());
  }
  public static dafny.DafnyMap<? extends java.lang.Byte, ? extends java.math.BigInteger> charToDigit()
  {
    return dafny.DafnyMap.fromElements(new dafny.Tuple2(((byte) ('0')), java.math.BigInteger.ZERO), new dafny.Tuple2(((byte) ('1')), java.math.BigInteger.ONE), new dafny.Tuple2(((byte) ('2')), java.math.BigInteger.valueOf(2L)), new dafny.Tuple2(((byte) ('3')), java.math.BigInteger.valueOf(3L)), new dafny.Tuple2(((byte) ('4')), java.math.BigInteger.valueOf(4L)), new dafny.Tuple2(((byte) ('5')), java.math.BigInteger.valueOf(5L)), new dafny.Tuple2(((byte) ('6')), java.math.BigInteger.valueOf(6L)), new dafny.Tuple2(((byte) ('7')), java.math.BigInteger.valueOf(7L)), new dafny.Tuple2(((byte) ('8')), java.math.BigInteger.valueOf(8L)), new dafny.Tuple2(((byte) ('9')), java.math.BigInteger.valueOf(9L)));
  }
  @Override
  public java.lang.String toString() {
    return "Std.JSON.ByteStrConversion._default";
  }
}
