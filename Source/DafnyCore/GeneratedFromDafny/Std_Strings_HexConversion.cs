// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;

namespace Std.Strings.HexConversion {

  public partial class __default {
    public static BigInteger BASE() {
      return Std.Strings.HexConversion.__default.@base;
    }
    public static bool IsDigitChar(Dafny.Rune c) {
      return (Std.Strings.HexConversion.__default.charToDigit).Contains(c);
    }
    public static Dafny.ISequence<Dafny.Rune> OfDigits(Dafny.ISequence<BigInteger> digits) {
      Dafny.ISequence<Dafny.Rune> _153___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((digits).Equals(Dafny.Sequence<BigInteger>.FromElements())) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.FromElements(), _153___accumulator);
      } else {
        _153___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.FromElements((Std.Strings.HexConversion.__default.chars).Select((digits).Select(BigInteger.Zero))), _153___accumulator);
        Dafny.ISequence<BigInteger> _in46 = (digits).Drop(BigInteger.One);
        digits = _in46;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> OfNat(BigInteger n) {
      if ((n).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.FromElements((Std.Strings.HexConversion.__default.chars).Select(BigInteger.Zero));
      } else {
        return Std.Strings.HexConversion.__default.OfDigits(Std.Strings.HexConversion.__default.FromNat(n));
      }
    }
    public static bool IsNumberStr(Dafny.ISequence<Dafny.Rune> str, Dafny.Rune minus)
    {
      return !(!(str).Equals(Dafny.Sequence<Dafny.Rune>.FromElements())) || (((((str).Select(BigInteger.Zero)) == (minus)) || ((Std.Strings.HexConversion.__default.charToDigit).Contains((str).Select(BigInteger.Zero)))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, bool>>((_154_str) => Dafny.Helpers.Quantifier<Dafny.Rune>(((_154_str).Drop(BigInteger.One)).UniqueElements, true, (((_forall_var_1) => {
        Dafny.Rune _155_c = (Dafny.Rune)_forall_var_1;
        return !(((_154_str).Drop(BigInteger.One)).Contains(_155_c)) || (Std.Strings.HexConversion.__default.IsDigitChar(_155_c));
      }))))(str)));
    }
    public static Dafny.ISequence<Dafny.Rune> OfInt(BigInteger n, Dafny.Rune minus)
    {
      if ((n).Sign != -1) {
        return Std.Strings.HexConversion.__default.OfNat(n);
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.FromElements(minus), Std.Strings.HexConversion.__default.OfNat((BigInteger.Zero) - (n)));
      }
    }
    public static BigInteger ToNat(Dafny.ISequence<Dafny.Rune> str) {
      if ((str).Equals(Dafny.Sequence<Dafny.Rune>.FromElements())) {
        return BigInteger.Zero;
      } else {
        Dafny.Rune _156_c = (str).Select((new BigInteger((str).Count)) - (BigInteger.One));
        return ((Std.Strings.HexConversion.__default.ToNat((str).Take((new BigInteger((str).Count)) - (BigInteger.One)))) * (Std.Strings.HexConversion.__default.@base)) + (Dafny.Map<Dafny.Rune, BigInteger>.Select(Std.Strings.HexConversion.__default.charToDigit,_156_c));
      }
    }
    public static BigInteger ToInt(Dafny.ISequence<Dafny.Rune> str, Dafny.Rune minus)
    {
      if (Dafny.Sequence<Dafny.Rune>.IsPrefixOf(Dafny.Sequence<Dafny.Rune>.FromElements(minus), str)) {
        return (BigInteger.Zero) - (Std.Strings.HexConversion.__default.ToNat((str).Drop(BigInteger.One)));
      } else {
        return Std.Strings.HexConversion.__default.ToNat(str);
      }
    }
    public static BigInteger ToNatRight(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else {
        return ((Std.Strings.HexConversion.__default.ToNatRight(Std.Collections.Seq.__default.DropFirst<BigInteger>(xs))) * (Std.Strings.HexConversion.__default.BASE())) + (Std.Collections.Seq.__default.First<BigInteger>(xs));
      }
    }
    public static BigInteger ToNatLeft(Dafny.ISequence<BigInteger> xs) {
      BigInteger _157___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_157___accumulator);
      } else {
        _157___accumulator = ((Std.Collections.Seq.__default.Last<BigInteger>(xs)) * (Std.Arithmetic.Power.__default.Pow(Std.Strings.HexConversion.__default.BASE(), (new BigInteger((xs).Count)) - (BigInteger.One)))) + (_157___accumulator);
        Dafny.ISequence<BigInteger> _in47 = Std.Collections.Seq.__default.DropLast<BigInteger>(xs);
        xs = _in47;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> FromNat(BigInteger n) {
      Dafny.ISequence<BigInteger> _158___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((n).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_158___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _158___accumulator = Dafny.Sequence<BigInteger>.Concat(_158___accumulator, Dafny.Sequence<BigInteger>.FromElements(Dafny.Helpers.EuclideanModulus(n, Std.Strings.HexConversion.__default.BASE())));
        BigInteger _in48 = Dafny.Helpers.EuclideanDivision(n, Std.Strings.HexConversion.__default.BASE());
        n = _in48;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtend(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)) >= (n)) {
        return xs;
      } else {
        Dafny.ISequence<BigInteger> _in49 = Dafny.Sequence<BigInteger>.Concat(xs, Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero));
        BigInteger _in50 = n;
        xs = _in49;
        n = _in50;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtendMultiple(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
      BigInteger _159_newLen = ((new BigInteger((xs).Count)) + (n)) - (Dafny.Helpers.EuclideanModulus(new BigInteger((xs).Count), n));
      return Std.Strings.HexConversion.__default.SeqExtend(xs, _159_newLen);
    }
    public static Dafny.ISequence<BigInteger> FromNatWithLen(BigInteger n, BigInteger len)
    {
      return Std.Strings.HexConversion.__default.SeqExtend(Std.Strings.HexConversion.__default.FromNat(n), len);
    }
    public static Dafny.ISequence<BigInteger> SeqZero(BigInteger len) {
      Dafny.ISequence<BigInteger> _160_xs = Std.Strings.HexConversion.__default.FromNatWithLen(BigInteger.Zero, len);
      return _160_xs;
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqAdd(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs1 = Std.Strings.HexConversion.__default.SeqAdd(Std.Collections.Seq.__default.DropLast<BigInteger>(xs), Std.Collections.Seq.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _161_zs_k = _let_tmp_rhs1.dtor__0;
        BigInteger _162_cin = _let_tmp_rhs1.dtor__1;
        BigInteger _163_sum = ((Std.Collections.Seq.__default.Last<BigInteger>(xs)) + (Std.Collections.Seq.__default.Last<BigInteger>(ys))) + (_162_cin);
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs2 = (((_163_sum) < (Std.Strings.HexConversion.__default.BASE())) ? (_System.Tuple2<BigInteger, BigInteger>.create(_163_sum, BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((_163_sum) - (Std.Strings.HexConversion.__default.BASE()), BigInteger.One)));
        BigInteger _164_sum__out = _let_tmp_rhs2.dtor__0;
        BigInteger _165_cout = _let_tmp_rhs2.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_161_zs_k, Dafny.Sequence<BigInteger>.FromElements(_164_sum__out)), _165_cout);
      }
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqSub(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs3 = Std.Strings.HexConversion.__default.SeqSub(Std.Collections.Seq.__default.DropLast<BigInteger>(xs), Std.Collections.Seq.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _166_zs = _let_tmp_rhs3.dtor__0;
        BigInteger _167_cin = _let_tmp_rhs3.dtor__1;
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs4 = (((Std.Collections.Seq.__default.Last<BigInteger>(xs)) >= ((Std.Collections.Seq.__default.Last<BigInteger>(ys)) + (_167_cin))) ? (_System.Tuple2<BigInteger, BigInteger>.create(((Std.Collections.Seq.__default.Last<BigInteger>(xs)) - (Std.Collections.Seq.__default.Last<BigInteger>(ys))) - (_167_cin), BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((((Std.Strings.HexConversion.__default.BASE()) + (Std.Collections.Seq.__default.Last<BigInteger>(xs))) - (Std.Collections.Seq.__default.Last<BigInteger>(ys))) - (_167_cin), BigInteger.One)));
        BigInteger _168_diff__out = _let_tmp_rhs4.dtor__0;
        BigInteger _169_cout = _let_tmp_rhs4.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_166_zs, Dafny.Sequence<BigInteger>.FromElements(_168_diff__out)), _169_cout);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> HEX__DIGITS { get {
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0123456789ABCDEF");
    } }
    public static Dafny.ISequence<Dafny.Rune> chars { get {
      return Std.Strings.HexConversion.__default.HEX__DIGITS;
    } }
    public static BigInteger @base { get {
      return new BigInteger((Std.Strings.HexConversion.__default.chars).Count);
    } }
    public static Dafny.IMap<Dafny.Rune,BigInteger> charToDigit { get {
      return Dafny.Map<Dafny.Rune, BigInteger>.FromElements(new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('0'), BigInteger.Zero), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('1'), BigInteger.One), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('2'), new BigInteger(2)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('3'), new BigInteger(3)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('4'), new BigInteger(4)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('5'), new BigInteger(5)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('6'), new BigInteger(6)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('7'), new BigInteger(7)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('8'), new BigInteger(8)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('9'), new BigInteger(9)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('a'), new BigInteger(10)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('b'), new BigInteger(11)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('c'), new BigInteger(12)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('d'), new BigInteger(13)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('e'), new BigInteger(14)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('f'), new BigInteger(15)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('A'), new BigInteger(10)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('B'), new BigInteger(11)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('C'), new BigInteger(12)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('D'), new BigInteger(13)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('E'), new BigInteger(14)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('F'), new BigInteger(15)));
    } }
  }

  public partial class CharSeq {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>>(Dafny.Sequence<Dafny.Rune>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(Dafny.ISequence<Dafny.Rune> __source) {
      Dafny.ISequence<Dafny.Rune> _170_chars = __source;
      return (new BigInteger((_170_chars).Count)) > (BigInteger.One);
    }
  }

  public partial class digit {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(BigInteger __source) {
      BigInteger _171_i = __source;
      if (_System.nat._Is(_171_i)) {
        return ((_171_i).Sign != -1) && ((_171_i) < (Std.Strings.HexConversion.__default.BASE()));
      }
      return false;
    }
  }
} // end of namespace Std.Strings.HexConversion