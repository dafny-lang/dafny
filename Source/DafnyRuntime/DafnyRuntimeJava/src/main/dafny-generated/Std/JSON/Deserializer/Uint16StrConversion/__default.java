// Class __default
// Dafny class __default compiled into Java
package Std.JSON.Deserializer.Uint16StrConversion;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static java.math.BigInteger BASE() {
    return __default.base();
  }
  public static boolean IsDigitChar(short c) {
    return (__default.charToDigit()).<java.lang.Short>contains(c);
  }
  public static dafny.DafnySequence<? extends java.lang.Short> OfDigits(dafny.DafnySequence<? extends java.math.BigInteger> digits) {
    dafny.DafnySequence<? extends java.lang.Short> _483___accumulator = dafny.DafnySequence.<java.lang.Short> empty(Std.BoundedInts.uint16._typeDescriptor());
    TAIL_CALL_START: while (true) {
      if ((digits).equals(dafny.DafnySequence.<java.math.BigInteger> empty(dafny.TypeDescriptor.BIG_INTEGER))) {
        return dafny.DafnySequence.<java.lang.Short>concatenate(dafny.DafnySequence.<java.lang.Short> empty(Std.BoundedInts.uint16._typeDescriptor()), _483___accumulator);
      } else {
        _483___accumulator = dafny.DafnySequence.<java.lang.Short>concatenate(dafny.DafnySequence.<java.lang.Short> of(((short)(java.lang.Object)((__default.chars()).select(dafny.Helpers.toInt((((java.math.BigInteger)(java.lang.Object)((digits).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))))))))), _483___accumulator);
        dafny.DafnySequence<? extends java.math.BigInteger> _in81 = (digits).drop(java.math.BigInteger.ONE);
        digits = _in81;
        continue TAIL_CALL_START;
      }
    }
  }
  public static dafny.DafnySequence<? extends java.lang.Short> OfNat(java.math.BigInteger n) {
    if ((n).signum() == 0) {
      return dafny.DafnySequence.<java.lang.Short> of(((short)(java.lang.Object)((__default.chars()).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))));
    } else {
      return __default.OfDigits(__default.FromNat(n));
    }
  }
  public static boolean IsNumberStr(dafny.DafnySequence<? extends java.lang.Short> str, short minus)
  {
    return !(!(str).equals(dafny.DafnySequence.<java.lang.Short> empty(Std.BoundedInts.uint16._typeDescriptor()))) || ((((((short)(java.lang.Object)((str).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))))) == (minus)) || ((__default.charToDigit()).<java.lang.Short>contains(((short)(java.lang.Object)((str).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))))))) && (((java.util.function.Function<dafny.DafnySequence<? extends java.lang.Short>, Boolean>)(_484_str) -> dafny.Helpers.Quantifier(((_484_str).drop(java.math.BigInteger.ONE)).UniqueElements(), true, ((_forall_var_4_boxed0) -> {
      short _forall_var_4 = ((short)(java.lang.Object)(_forall_var_4_boxed0));
      if (true) {
        short _485_c = (short)_forall_var_4;
        return !(((_484_str).drop(java.math.BigInteger.ONE)).contains(_485_c)) || (__default.IsDigitChar(_485_c));
      } else {
        return true;
      }
    }))).apply(str)));
  }
  public static dafny.DafnySequence<? extends java.lang.Short> OfInt(java.math.BigInteger n, short minus)
  {
    if ((n).signum() != -1) {
      return __default.OfNat(n);
    } else {
      return dafny.DafnySequence.<java.lang.Short>concatenate(dafny.DafnySequence.<java.lang.Short> of(minus), __default.OfNat((java.math.BigInteger.ZERO).subtract(n)));
    }
  }
  public static java.math.BigInteger ToNat(dafny.DafnySequence<? extends java.lang.Short> str) {
    if ((str).equals(dafny.DafnySequence.<java.lang.Short> empty(Std.BoundedInts.uint16._typeDescriptor()))) {
      return java.math.BigInteger.ZERO;
    } else {
      short _486_c = ((short)(java.lang.Object)((str).select(dafny.Helpers.toInt(((java.math.BigInteger.valueOf((str).length())).subtract(java.math.BigInteger.ONE))))));
      return ((__default.ToNat((str).take((java.math.BigInteger.valueOf((str).length())).subtract(java.math.BigInteger.ONE)))).multiply(__default.base())).add(((java.math.BigInteger)(java.lang.Object)((__default.charToDigit()).get(_486_c))));
    }
  }
  public static java.math.BigInteger ToInt(dafny.DafnySequence<? extends java.lang.Short> str, short minus)
  {
    if ((dafny.DafnySequence.<java.lang.Short> of(minus)).isPrefixOf(str)) {
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
    java.math.BigInteger _487___accumulator = java.math.BigInteger.ZERO;
    TAIL_CALL_START: while (true) {
      if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
        return (java.math.BigInteger.ZERO).add(_487___accumulator);
      } else {
        _487___accumulator = ((Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, xs)).multiply(Std.Arithmetic.Power.__default.Pow(__default.BASE(), (java.math.BigInteger.valueOf((xs).length())).subtract(java.math.BigInteger.ONE)))).add(_487___accumulator);
        dafny.DafnySequence<? extends java.math.BigInteger> _in82 = Std.Collections.Seq.__default.<java.math.BigInteger>DropLast(digit._typeDescriptor(), xs);
        xs = _in82;
        continue TAIL_CALL_START;
      }
    }
  }
  public static dafny.DafnySequence<? extends java.math.BigInteger> FromNat(java.math.BigInteger n) {
    dafny.DafnySequence<? extends java.math.BigInteger> _488___accumulator = dafny.DafnySequence.<java.math.BigInteger> empty(digit._typeDescriptor());
    TAIL_CALL_START: while (true) {
      if ((n).signum() == 0) {
        return dafny.DafnySequence.<java.math.BigInteger>concatenate(_488___accumulator, dafny.DafnySequence.<java.math.BigInteger> empty(dafny.TypeDescriptor.BIG_INTEGER));
      } else {
        _488___accumulator = dafny.DafnySequence.<java.math.BigInteger>concatenate(_488___accumulator, dafny.DafnySequence.<java.math.BigInteger> of(dafny.TypeDescriptor.BIG_INTEGER, dafny.DafnyEuclidean.EuclideanModulus(n, __default.BASE())));
        java.math.BigInteger _in83 = dafny.DafnyEuclidean.EuclideanDivision(n, __default.BASE());
        n = _in83;
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
        dafny.DafnySequence<? extends java.math.BigInteger> _in84 = dafny.DafnySequence.<java.math.BigInteger>concatenate(xs, dafny.DafnySequence.<java.math.BigInteger> of(digit._typeDescriptor(), java.math.BigInteger.ZERO));
        java.math.BigInteger _in85 = n;
        xs = _in84;
        n = _in85;
        continue TAIL_CALL_START;
      }
    }
  }
  public static dafny.DafnySequence<? extends java.math.BigInteger> SeqExtendMultiple(dafny.DafnySequence<? extends java.math.BigInteger> xs, java.math.BigInteger n)
  {
    java.math.BigInteger _489_newLen = ((java.math.BigInteger.valueOf((xs).length())).add(n)).subtract(dafny.DafnyEuclidean.EuclideanModulus(java.math.BigInteger.valueOf((xs).length()), n));
    return __default.SeqExtend(xs, _489_newLen);
  }
  public static dafny.DafnySequence<? extends java.math.BigInteger> FromNatWithLen(java.math.BigInteger n, java.math.BigInteger len)
  {
    return __default.SeqExtend(__default.FromNat(n), len);
  }
  public static dafny.DafnySequence<? extends java.math.BigInteger> SeqZero(java.math.BigInteger len) {
    dafny.DafnySequence<? extends java.math.BigInteger> _490_xs = __default.FromNatWithLen(java.math.BigInteger.ZERO, len);
    return _490_xs;
  }
  public static dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger> SeqAdd(dafny.DafnySequence<? extends java.math.BigInteger> xs, dafny.DafnySequence<? extends java.math.BigInteger> ys)
  {
    if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
      return dafny.Tuple2.<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>create(dafny.DafnySequence.<java.math.BigInteger> empty(dafny.TypeDescriptor.BIG_INTEGER), java.math.BigInteger.ZERO);
    } else {
      dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger> _let_tmp_rhs13 = __default.SeqAdd(Std.Collections.Seq.__default.<java.math.BigInteger>DropLast(digit._typeDescriptor(), xs), Std.Collections.Seq.__default.<java.math.BigInteger>DropLast(digit._typeDescriptor(), ys));
      dafny.DafnySequence<? extends java.math.BigInteger> _491_zs_k = ((dafny.DafnySequence<? extends java.math.BigInteger>)(java.lang.Object)(((dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>)_let_tmp_rhs13).dtor__0()));
      java.math.BigInteger _492_cin = ((java.math.BigInteger)(java.lang.Object)(((dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>)_let_tmp_rhs13).dtor__1()));
      java.math.BigInteger _493_sum = ((Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, xs)).add(Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, ys))).add(_492_cin);
      dafny.Tuple2<java.math.BigInteger, java.math.BigInteger> _let_tmp_rhs14 = (((_493_sum).compareTo(__default.BASE()) < 0) ? (dafny.Tuple2.<java.math.BigInteger, java.math.BigInteger>create(_493_sum, java.math.BigInteger.ZERO)) : (dafny.Tuple2.<java.math.BigInteger, java.math.BigInteger>create((_493_sum).subtract(__default.BASE()), java.math.BigInteger.ONE)));
      java.math.BigInteger _494_sum__out = ((java.math.BigInteger)(java.lang.Object)(((dafny.Tuple2<java.math.BigInteger, java.math.BigInteger>)_let_tmp_rhs14).dtor__0()));
      java.math.BigInteger _495_cout = ((java.math.BigInteger)(java.lang.Object)(((dafny.Tuple2<java.math.BigInteger, java.math.BigInteger>)_let_tmp_rhs14).dtor__1()));
      return dafny.Tuple2.<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>create(dafny.DafnySequence.<java.math.BigInteger>concatenate(_491_zs_k, dafny.DafnySequence.<java.math.BigInteger> of(dafny.TypeDescriptor.BIG_INTEGER, _494_sum__out)), _495_cout);
    }
  }
  public static dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger> SeqSub(dafny.DafnySequence<? extends java.math.BigInteger> xs, dafny.DafnySequence<? extends java.math.BigInteger> ys)
  {
    if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
      return dafny.Tuple2.<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>create(dafny.DafnySequence.<java.math.BigInteger> empty(dafny.TypeDescriptor.BIG_INTEGER), java.math.BigInteger.ZERO);
    } else {
      dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger> _let_tmp_rhs15 = __default.SeqSub(Std.Collections.Seq.__default.<java.math.BigInteger>DropLast(digit._typeDescriptor(), xs), Std.Collections.Seq.__default.<java.math.BigInteger>DropLast(digit._typeDescriptor(), ys));
      dafny.DafnySequence<? extends java.math.BigInteger> _496_zs = ((dafny.DafnySequence<? extends java.math.BigInteger>)(java.lang.Object)(((dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>)_let_tmp_rhs15).dtor__0()));
      java.math.BigInteger _497_cin = ((java.math.BigInteger)(java.lang.Object)(((dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>)_let_tmp_rhs15).dtor__1()));
      dafny.Tuple2<java.math.BigInteger, java.math.BigInteger> _let_tmp_rhs16 = (((Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, xs)).compareTo((Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, ys)).add(_497_cin)) >= 0) ? (dafny.Tuple2.<java.math.BigInteger, java.math.BigInteger>create(((Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, xs)).subtract(Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, ys))).subtract(_497_cin), java.math.BigInteger.ZERO)) : (dafny.Tuple2.<java.math.BigInteger, java.math.BigInteger>create((((__default.BASE()).add(Std.Collections.Seq.__default.<java.math.BigInteger>Last(digit._typeDescriptor(), xs))).subtract(Std.Collections.Seq.__default.<java.math.BigInteger>Last(digit._typeDescriptor(), ys))).subtract(_497_cin), java.math.BigInteger.ONE)));
      java.math.BigInteger _498_diff__out = ((java.math.BigInteger)(java.lang.Object)(((dafny.Tuple2<java.math.BigInteger, java.math.BigInteger>)_let_tmp_rhs16).dtor__0()));
      java.math.BigInteger _499_cout = ((java.math.BigInteger)(java.lang.Object)(((dafny.Tuple2<java.math.BigInteger, java.math.BigInteger>)_let_tmp_rhs16).dtor__1()));
      return dafny.Tuple2.<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>create(dafny.DafnySequence.<java.math.BigInteger>concatenate(_496_zs, dafny.DafnySequence.<java.math.BigInteger> of(dafny.TypeDescriptor.BIG_INTEGER, _498_diff__out)), _499_cout);
    }
  }
  public static dafny.DafnySequence<? extends java.lang.Short> chars()
  {
    return dafny.DafnySequence.<java.lang.Short> of(((short) ('0')), ((short) ('1')), ((short) ('2')), ((short) ('3')), ((short) ('4')), ((short) ('5')), ((short) ('6')), ((short) ('7')), ((short) ('8')), ((short) ('9')), ((short) ('a')), ((short) ('b')), ((short) ('c')), ((short) ('d')), ((short) ('e')), ((short) ('f')), ((short) ('A')), ((short) ('B')), ((short) ('C')), ((short) ('D')), ((short) ('E')), ((short) ('F')));
  }
  public static java.math.BigInteger base()
  {
    return java.math.BigInteger.valueOf((__default.chars()).length());
  }
  public static dafny.DafnyMap<? extends java.lang.Short, ? extends java.math.BigInteger> charToDigit()
  {
    return dafny.DafnyMap.fromElements(new dafny.Tuple2(((short) ('0')), java.math.BigInteger.ZERO), new dafny.Tuple2(((short) ('1')), java.math.BigInteger.ONE), new dafny.Tuple2(((short) ('2')), java.math.BigInteger.valueOf(2L)), new dafny.Tuple2(((short) ('3')), java.math.BigInteger.valueOf(3L)), new dafny.Tuple2(((short) ('4')), java.math.BigInteger.valueOf(4L)), new dafny.Tuple2(((short) ('5')), java.math.BigInteger.valueOf(5L)), new dafny.Tuple2(((short) ('6')), java.math.BigInteger.valueOf(6L)), new dafny.Tuple2(((short) ('7')), java.math.BigInteger.valueOf(7L)), new dafny.Tuple2(((short) ('8')), java.math.BigInteger.valueOf(8L)), new dafny.Tuple2(((short) ('9')), java.math.BigInteger.valueOf(9L)), new dafny.Tuple2(((short) ('a')), java.math.BigInteger.valueOf(10L)), new dafny.Tuple2(((short) ('b')), java.math.BigInteger.valueOf(11L)), new dafny.Tuple2(((short) ('c')), java.math.BigInteger.valueOf(12L)), new dafny.Tuple2(((short) ('d')), java.math.BigInteger.valueOf(13L)), new dafny.Tuple2(((short) ('e')), java.math.BigInteger.valueOf(14L)), new dafny.Tuple2(((short) ('f')), java.math.BigInteger.valueOf(15L)), new dafny.Tuple2(((short) ('A')), java.math.BigInteger.valueOf(10L)), new dafny.Tuple2(((short) ('B')), java.math.BigInteger.valueOf(11L)), new dafny.Tuple2(((short) ('C')), java.math.BigInteger.valueOf(12L)), new dafny.Tuple2(((short) ('D')), java.math.BigInteger.valueOf(13L)), new dafny.Tuple2(((short) ('E')), java.math.BigInteger.valueOf(14L)), new dafny.Tuple2(((short) ('F')), java.math.BigInteger.valueOf(15L)));
  }
  @Override
  public java.lang.String toString() {
    return "Std.JSON.Deserializer.Uint16StrConversion._default";
  }
}
