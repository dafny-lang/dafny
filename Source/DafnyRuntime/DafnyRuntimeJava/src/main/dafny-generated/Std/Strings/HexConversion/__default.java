// Class __default
// Dafny class __default compiled into Java
package Std.Strings.HexConversion;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static java.math.BigInteger BASE() {
    return __default.base();
  }
  public static dafny.DafnySequence<? extends dafny.CodePoint> OfDigits(dafny.DafnySequence<? extends java.math.BigInteger> digits) {
    dafny.DafnySequence<? extends dafny.CodePoint> _135___accumulator = dafny.DafnySequence.<dafny.CodePoint> empty(dafny.TypeDescriptor.UNICODE_CHAR);
    TAIL_CALL_START: while (true) {
      if ((digits).equals(dafny.DafnySequence.<java.math.BigInteger> empty(dafny.TypeDescriptor.BIG_INTEGER))) {
        return dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.<dafny.CodePoint> empty(dafny.TypeDescriptor.UNICODE_CHAR), _135___accumulator);
      } else {
        _135___accumulator = dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.<dafny.CodePoint> of(dafny.TypeDescriptor.UNICODE_CHAR, dafny.CodePoint.valueOf(((dafny.CodePoint)((__default.chars()).select(dafny.Helpers.toInt((((java.math.BigInteger)(java.lang.Object)((digits).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))))))))).value())), _135___accumulator);
        dafny.DafnySequence<? extends java.math.BigInteger> _in42 = (digits).drop(java.math.BigInteger.ONE);
        digits = _in42;
        continue TAIL_CALL_START;
      }
    }
  }
  public static dafny.DafnySequence<? extends dafny.CodePoint> OfNat(java.math.BigInteger n) {
    if ((n).signum() == 0) {
      return dafny.DafnySequence.<dafny.CodePoint> of(dafny.TypeDescriptor.UNICODE_CHAR, dafny.CodePoint.valueOf(((dafny.CodePoint)((__default.chars()).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))).value()));
    } else {
      return __default.OfDigits(__default.FromNat(n));
    }
  }
  public static boolean OfNumberStr(dafny.DafnySequence<? extends dafny.CodePoint> str, int minus)
  {
    return !(!(str).equals(dafny.DafnySequence.<dafny.CodePoint> empty(dafny.TypeDescriptor.UNICODE_CHAR))) || ((((((dafny.CodePoint)((str).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))).value()) == (minus)) || ((__default.chars()).contains(dafny.CodePoint.valueOf(((dafny.CodePoint)((str).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))).value())))) && (((java.util.function.Function<dafny.DafnySequence<? extends dafny.CodePoint>, Boolean>)(_136_str) -> dafny.Helpers.Quantifier(((_136_str).drop(java.math.BigInteger.ONE)).UniqueElements(), true, ((_forall_var_1_boxed0) -> {
      int _forall_var_1 = ((dafny.CodePoint)(_forall_var_1_boxed0)).value();
      if (true) {
        int _137_c = (int)_forall_var_1;
        return !(((_136_str).drop(java.math.BigInteger.ONE)).contains(dafny.CodePoint.valueOf(_137_c))) || ((__default.chars()).contains(dafny.CodePoint.valueOf(_137_c)));
      } else {
        return true;
      }
    }))).apply(str)));
  }
  public static boolean ToNumberStr(dafny.DafnySequence<? extends dafny.CodePoint> str, int minus)
  {
    return !(!(str).equals(dafny.DafnySequence.<dafny.CodePoint> empty(dafny.TypeDescriptor.UNICODE_CHAR))) || ((((((dafny.CodePoint)((str).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))).value()) == (minus)) || ((__default.charToDigit()).<dafny.CodePoint>contains(dafny.CodePoint.valueOf(((dafny.CodePoint)((str).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))).value())))) && (((java.util.function.Function<dafny.DafnySequence<? extends dafny.CodePoint>, Boolean>)(_138_str) -> dafny.Helpers.Quantifier(((_138_str).drop(java.math.BigInteger.ONE)).UniqueElements(), true, ((_forall_var_2_boxed0) -> {
      int _forall_var_2 = ((dafny.CodePoint)(_forall_var_2_boxed0)).value();
      if (true) {
        int _139_c = (int)_forall_var_2;
        return !(((_138_str).drop(java.math.BigInteger.ONE)).contains(dafny.CodePoint.valueOf(_139_c))) || ((__default.charToDigit()).<dafny.CodePoint>contains(dafny.CodePoint.valueOf(_139_c)));
      } else {
        return true;
      }
    }))).apply(str)));
  }
  public static dafny.DafnySequence<? extends dafny.CodePoint> OfInt(java.math.BigInteger n, int minus)
  {
    if ((n).signum() != -1) {
      return __default.OfNat(n);
    } else {
      return dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.<dafny.CodePoint> of(dafny.TypeDescriptor.UNICODE_CHAR, dafny.CodePoint.valueOf(minus)), __default.OfNat((java.math.BigInteger.ZERO).subtract(n)));
    }
  }
  public static java.math.BigInteger ToNat(dafny.DafnySequence<? extends dafny.CodePoint> str) {
    if ((str).equals(dafny.DafnySequence.<dafny.CodePoint> empty(dafny.TypeDescriptor.UNICODE_CHAR))) {
      return java.math.BigInteger.ZERO;
    } else {
      return ((__default.ToNat((str).take((java.math.BigInteger.valueOf((str).length())).subtract(java.math.BigInteger.ONE)))).multiply(__default.base())).add(((java.math.BigInteger)(java.lang.Object)((__default.charToDigit()).get(dafny.CodePoint.valueOf(((dafny.CodePoint)((str).select(dafny.Helpers.toInt(((java.math.BigInteger.valueOf((str).length())).subtract(java.math.BigInteger.ONE)))))).value())))));
    }
  }
  public static java.math.BigInteger ToInt(dafny.DafnySequence<? extends dafny.CodePoint> str, int minus)
  {
    if ((dafny.DafnySequence.<dafny.CodePoint> of(dafny.TypeDescriptor.UNICODE_CHAR, dafny.CodePoint.valueOf(minus))).isPrefixOf(str)) {
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
    java.math.BigInteger _140___accumulator = java.math.BigInteger.ZERO;
    TAIL_CALL_START: while (true) {
      if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
        return (java.math.BigInteger.ZERO).add(_140___accumulator);
      } else {
        _140___accumulator = ((Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, xs)).multiply(Std.Arithmetic.Power.__default.Pow(__default.BASE(), (java.math.BigInteger.valueOf((xs).length())).subtract(java.math.BigInteger.ONE)))).add(_140___accumulator);
        dafny.DafnySequence<? extends java.math.BigInteger> _in43 = Std.Collections.Seq.__default.<java.math.BigInteger>DropLast(digit._typeDescriptor(), xs);
        xs = _in43;
        continue TAIL_CALL_START;
      }
    }
  }
  public static dafny.DafnySequence<? extends java.math.BigInteger> FromNat(java.math.BigInteger n) {
    dafny.DafnySequence<? extends java.math.BigInteger> _141___accumulator = dafny.DafnySequence.<java.math.BigInteger> empty(digit._typeDescriptor());
    TAIL_CALL_START: while (true) {
      if ((n).signum() == 0) {
        return dafny.DafnySequence.<java.math.BigInteger>concatenate(_141___accumulator, dafny.DafnySequence.<java.math.BigInteger> empty(dafny.TypeDescriptor.BIG_INTEGER));
      } else {
        _141___accumulator = dafny.DafnySequence.<java.math.BigInteger>concatenate(_141___accumulator, dafny.DafnySequence.<java.math.BigInteger> of(dafny.TypeDescriptor.BIG_INTEGER, dafny.DafnyEuclidean.EuclideanModulus(n, __default.BASE())));
        java.math.BigInteger _in44 = dafny.DafnyEuclidean.EuclideanDivision(n, __default.BASE());
        n = _in44;
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
        dafny.DafnySequence<? extends java.math.BigInteger> _in45 = dafny.DafnySequence.<java.math.BigInteger>concatenate(xs, dafny.DafnySequence.<java.math.BigInteger> of(digit._typeDescriptor(), java.math.BigInteger.ZERO));
        java.math.BigInteger _in46 = n;
        xs = _in45;
        n = _in46;
        continue TAIL_CALL_START;
      }
    }
  }
  public static dafny.DafnySequence<? extends java.math.BigInteger> SeqExtendMultiple(dafny.DafnySequence<? extends java.math.BigInteger> xs, java.math.BigInteger n)
  {
    java.math.BigInteger _142_newLen = ((java.math.BigInteger.valueOf((xs).length())).add(n)).subtract(dafny.DafnyEuclidean.EuclideanModulus(java.math.BigInteger.valueOf((xs).length()), n));
    return __default.SeqExtend(xs, _142_newLen);
  }
  public static dafny.DafnySequence<? extends java.math.BigInteger> FromNatWithLen(java.math.BigInteger n, java.math.BigInteger len)
  {
    return __default.SeqExtend(__default.FromNat(n), len);
  }
  public static dafny.DafnySequence<? extends java.math.BigInteger> SeqZero(java.math.BigInteger len) {
    dafny.DafnySequence<? extends java.math.BigInteger> _143_xs = __default.FromNatWithLen(java.math.BigInteger.ZERO, len);
    return _143_xs;
  }
  public static dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger> SeqAdd(dafny.DafnySequence<? extends java.math.BigInteger> xs, dafny.DafnySequence<? extends java.math.BigInteger> ys)
  {
    if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
      return dafny.Tuple2.<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>create(dafny.DafnySequence.<java.math.BigInteger> empty(dafny.TypeDescriptor.BIG_INTEGER), java.math.BigInteger.ZERO);
    } else {
      dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger> _let_tmp_rhs1 = __default.SeqAdd(Std.Collections.Seq.__default.<java.math.BigInteger>DropLast(digit._typeDescriptor(), xs), Std.Collections.Seq.__default.<java.math.BigInteger>DropLast(digit._typeDescriptor(), ys));
      dafny.DafnySequence<? extends java.math.BigInteger> _144_zs_k = ((dafny.DafnySequence<? extends java.math.BigInteger>)(java.lang.Object)(((dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>)_let_tmp_rhs1).dtor__0()));
      java.math.BigInteger _145_cin = ((java.math.BigInteger)(java.lang.Object)(((dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>)_let_tmp_rhs1).dtor__1()));
      java.math.BigInteger _146_sum = ((Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, xs)).add(Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, ys))).add(_145_cin);
      dafny.Tuple2<java.math.BigInteger, java.math.BigInteger> _let_tmp_rhs2 = (((_146_sum).compareTo(__default.BASE()) < 0) ? (dafny.Tuple2.<java.math.BigInteger, java.math.BigInteger>create(_146_sum, java.math.BigInteger.ZERO)) : (dafny.Tuple2.<java.math.BigInteger, java.math.BigInteger>create((_146_sum).subtract(__default.BASE()), java.math.BigInteger.ONE)));
      java.math.BigInteger _147_sum__out = ((java.math.BigInteger)(java.lang.Object)(((dafny.Tuple2<java.math.BigInteger, java.math.BigInteger>)_let_tmp_rhs2).dtor__0()));
      java.math.BigInteger _148_cout = ((java.math.BigInteger)(java.lang.Object)(((dafny.Tuple2<java.math.BigInteger, java.math.BigInteger>)_let_tmp_rhs2).dtor__1()));
      return dafny.Tuple2.<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>create(dafny.DafnySequence.<java.math.BigInteger>concatenate(_144_zs_k, dafny.DafnySequence.<java.math.BigInteger> of(dafny.TypeDescriptor.BIG_INTEGER, _147_sum__out)), _148_cout);
    }
  }
  public static dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger> SeqSub(dafny.DafnySequence<? extends java.math.BigInteger> xs, dafny.DafnySequence<? extends java.math.BigInteger> ys)
  {
    if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
      return dafny.Tuple2.<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>create(dafny.DafnySequence.<java.math.BigInteger> empty(dafny.TypeDescriptor.BIG_INTEGER), java.math.BigInteger.ZERO);
    } else {
      dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger> _let_tmp_rhs3 = __default.SeqSub(Std.Collections.Seq.__default.<java.math.BigInteger>DropLast(digit._typeDescriptor(), xs), Std.Collections.Seq.__default.<java.math.BigInteger>DropLast(digit._typeDescriptor(), ys));
      dafny.DafnySequence<? extends java.math.BigInteger> _149_zs = ((dafny.DafnySequence<? extends java.math.BigInteger>)(java.lang.Object)(((dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>)_let_tmp_rhs3).dtor__0()));
      java.math.BigInteger _150_cin = ((java.math.BigInteger)(java.lang.Object)(((dafny.Tuple2<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>)_let_tmp_rhs3).dtor__1()));
      dafny.Tuple2<java.math.BigInteger, java.math.BigInteger> _let_tmp_rhs4 = (((Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, xs)).compareTo((Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, ys)).add(_150_cin)) >= 0) ? (dafny.Tuple2.<java.math.BigInteger, java.math.BigInteger>create(((Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, xs)).subtract(Std.Collections.Seq.__default.<java.math.BigInteger>Last(dafny.TypeDescriptor.BIG_INTEGER, ys))).subtract(_150_cin), java.math.BigInteger.ZERO)) : (dafny.Tuple2.<java.math.BigInteger, java.math.BigInteger>create((((__default.BASE()).add(Std.Collections.Seq.__default.<java.math.BigInteger>Last(digit._typeDescriptor(), xs))).subtract(Std.Collections.Seq.__default.<java.math.BigInteger>Last(digit._typeDescriptor(), ys))).subtract(_150_cin), java.math.BigInteger.ONE)));
      java.math.BigInteger _151_diff__out = ((java.math.BigInteger)(java.lang.Object)(((dafny.Tuple2<java.math.BigInteger, java.math.BigInteger>)_let_tmp_rhs4).dtor__0()));
      java.math.BigInteger _152_cout = ((java.math.BigInteger)(java.lang.Object)(((dafny.Tuple2<java.math.BigInteger, java.math.BigInteger>)_let_tmp_rhs4).dtor__1()));
      return dafny.Tuple2.<dafny.DafnySequence<? extends java.math.BigInteger>, java.math.BigInteger>create(dafny.DafnySequence.<java.math.BigInteger>concatenate(_149_zs, dafny.DafnySequence.<java.math.BigInteger> of(dafny.TypeDescriptor.BIG_INTEGER, _151_diff__out)), _152_cout);
    }
  }
  public static dafny.DafnySequence<? extends dafny.CodePoint> HEX__DIGITS()
  {
    return dafny.DafnySequence.asUnicodeString("0123456789ABCDEF");
  }
  public static dafny.DafnySequence<? extends dafny.CodePoint> chars()
  {
    return __default.HEX__DIGITS();
  }
  public static java.math.BigInteger base()
  {
    return java.math.BigInteger.valueOf((__default.chars()).length());
  }
  public static dafny.DafnyMap<? extends dafny.CodePoint, ? extends java.math.BigInteger> charToDigit()
  {
    return dafny.DafnyMap.fromElements(new dafny.Tuple2(dafny.CodePoint.valueOf('0'), java.math.BigInteger.ZERO), new dafny.Tuple2(dafny.CodePoint.valueOf('1'), java.math.BigInteger.ONE), new dafny.Tuple2(dafny.CodePoint.valueOf('2'), java.math.BigInteger.valueOf(2L)), new dafny.Tuple2(dafny.CodePoint.valueOf('3'), java.math.BigInteger.valueOf(3L)), new dafny.Tuple2(dafny.CodePoint.valueOf('4'), java.math.BigInteger.valueOf(4L)), new dafny.Tuple2(dafny.CodePoint.valueOf('5'), java.math.BigInteger.valueOf(5L)), new dafny.Tuple2(dafny.CodePoint.valueOf('6'), java.math.BigInteger.valueOf(6L)), new dafny.Tuple2(dafny.CodePoint.valueOf('7'), java.math.BigInteger.valueOf(7L)), new dafny.Tuple2(dafny.CodePoint.valueOf('8'), java.math.BigInteger.valueOf(8L)), new dafny.Tuple2(dafny.CodePoint.valueOf('9'), java.math.BigInteger.valueOf(9L)), new dafny.Tuple2(dafny.CodePoint.valueOf('a'), java.math.BigInteger.valueOf(10L)), new dafny.Tuple2(dafny.CodePoint.valueOf('b'), java.math.BigInteger.valueOf(11L)), new dafny.Tuple2(dafny.CodePoint.valueOf('c'), java.math.BigInteger.valueOf(12L)), new dafny.Tuple2(dafny.CodePoint.valueOf('d'), java.math.BigInteger.valueOf(13L)), new dafny.Tuple2(dafny.CodePoint.valueOf('e'), java.math.BigInteger.valueOf(14L)), new dafny.Tuple2(dafny.CodePoint.valueOf('f'), java.math.BigInteger.valueOf(15L)), new dafny.Tuple2(dafny.CodePoint.valueOf('A'), java.math.BigInteger.valueOf(10L)), new dafny.Tuple2(dafny.CodePoint.valueOf('B'), java.math.BigInteger.valueOf(11L)), new dafny.Tuple2(dafny.CodePoint.valueOf('C'), java.math.BigInteger.valueOf(12L)), new dafny.Tuple2(dafny.CodePoint.valueOf('D'), java.math.BigInteger.valueOf(13L)), new dafny.Tuple2(dafny.CodePoint.valueOf('E'), java.math.BigInteger.valueOf(14L)), new dafny.Tuple2(dafny.CodePoint.valueOf('F'), java.math.BigInteger.valueOf(15L)));
  }
  @Override
  public java.lang.String toString() {
    return "Std.Strings.HexConversion._default";
  }
}
