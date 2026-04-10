// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
#pragma warning disable CS0164 // This label has not been referenced
#pragma warning disable CS0162 // Unreachable code detected
#pragma warning disable CS1717 // Assignment made to same variable

namespace Std.Collections.Seq {

  public partial class __default {
    public static __T First<__T>(Dafny.ISequence<__T> xs) {
      return (xs).Select(BigInteger.Zero);
    }
    public static Dafny.ISequence<__T> DropFirst<__T>(Dafny.ISequence<__T> xs) {
      return (xs).Drop(BigInteger.One);
    }
    public static __T Last<__T>(Dafny.ISequence<__T> xs) {
      return (xs).Select((new BigInteger((xs).Count)) - (BigInteger.One));
    }
    public static Dafny.ISequence<__T> DropLast<__T>(Dafny.ISequence<__T> xs) {
      return (xs).Take((new BigInteger((xs).Count)) - (BigInteger.One));
    }
    public static __T[] ToArray<__T>(Dafny.ISequence<__T> xs)
    {
      __T[] a = new __T[0];
      Func<BigInteger, __T> _init0 = Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Func<BigInteger, __T>>>((_0_xs) => ((System.Func<BigInteger, __T>)((_1_i) => {
        return (_0_xs).Select(_1_i);
      })))(xs);
      __T[] _nw0 = new __T[Dafny.Helpers.ToIntChecked(new BigInteger((xs).Count), "array size exceeds memory limit")];
      for (var _i0_0 = 0; _i0_0 < new BigInteger(_nw0.Length); _i0_0++) {
        _nw0[(int)(_i0_0)] = _init0(_i0_0);
      }
      a = _nw0;
      return a;
    }
    public static Dafny.ISet<__T> ToSet<__T>(Dafny.ISequence<__T> xs) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Dafny.ISet<__T>>>((_0_xs) => ((System.Func<Dafny.ISet<__T>>)(() => {
        var _coll0 = new System.Collections.Generic.List<__T>();
        foreach (__T _compr_0 in (_0_xs).CloneAsArray()) {
          __T _1_x = (__T)_compr_0;
          if ((_0_xs).Contains(_1_x)) {
            _coll0.Add(_1_x);
          }
        }
        return Dafny.Set<__T>.FromCollection(_coll0);
      }))())(xs);
    }
    public static BigInteger IndexOf<__T>(Dafny.ISequence<__T> xs, __T v)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if (object.Equals((xs).Select(BigInteger.Zero), v)) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else {
        _0___accumulator = (_0___accumulator) + (BigInteger.One);
        Dafny.ISequence<__T> _in0 = (xs).Drop(BigInteger.One);
        __T _in1 = v;
        xs = _in0;
        v = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Std.Wrappers._IOption<BigInteger> IndexOfOption<__T>(Dafny.ISequence<__T> xs, __T v)
    {
      return Std.Collections.Seq.__default.IndexByOption<__T>(xs, Dafny.Helpers.Id<Func<__T, Func<__T, bool>>>((_0_v) => ((System.Func<__T, bool>)((_1_x) => {
        return object.Equals(_1_x, _0_v);
      })))(v));
    }
    public static Std.Wrappers._IOption<BigInteger> IndexByOption<__T>(Dafny.ISequence<__T> xs, Func<__T, bool> p)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Std.Wrappers.Option<BigInteger>.create_None();
      } else if (Dafny.Helpers.Id<Func<__T, bool>>(p)((xs).Select(BigInteger.Zero))) {
        return Std.Wrappers.Option<BigInteger>.create_Some(BigInteger.Zero);
      } else {
        Std.Wrappers._IOption<BigInteger> _0_o_k = Std.Collections.Seq.__default.IndexByOption<__T>((xs).Drop(BigInteger.One), p);
        if ((_0_o_k).is_Some) {
          return Std.Wrappers.Option<BigInteger>.create_Some(((_0_o_k).dtor_value) + (BigInteger.One));
        } else {
          return Std.Wrappers.Option<BigInteger>.create_None();
        }
      }
    }
    public static BigInteger LastIndexOf<__T>(Dafny.ISequence<__T> xs, __T v)
    {
    TAIL_CALL_START: ;
      if (object.Equals((xs).Select((new BigInteger((xs).Count)) - (BigInteger.One)), v)) {
        return (new BigInteger((xs).Count)) - (BigInteger.One);
      } else {
        Dafny.ISequence<__T> _in0 = (xs).Take((new BigInteger((xs).Count)) - (BigInteger.One));
        __T _in1 = v;
        xs = _in0;
        v = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Std.Wrappers._IOption<BigInteger> LastIndexOfOption<__T>(Dafny.ISequence<__T> xs, __T v)
    {
      return Std.Collections.Seq.__default.LastIndexByOption<__T>(xs, Dafny.Helpers.Id<Func<__T, Func<__T, bool>>>((_0_v) => ((System.Func<__T, bool>)((_1_x) => {
        return object.Equals(_1_x, _0_v);
      })))(v));
    }
    public static Std.Wrappers._IOption<BigInteger> LastIndexByOption<__T>(Dafny.ISequence<__T> xs, Func<__T, bool> p)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Std.Wrappers.Option<BigInteger>.create_None();
      } else if (Dafny.Helpers.Id<Func<__T, bool>>(p)((xs).Select((new BigInteger((xs).Count)) - (BigInteger.One)))) {
        return Std.Wrappers.Option<BigInteger>.create_Some((new BigInteger((xs).Count)) - (BigInteger.One));
      } else {
        Dafny.ISequence<__T> _in0 = (xs).Take((new BigInteger((xs).Count)) - (BigInteger.One));
        Func<__T, bool> _in1 = p;
        xs = _in0;
        p = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> Remove<__T>(Dafny.ISequence<__T> xs, BigInteger pos)
    {
      return Dafny.Sequence<__T>.Concat((xs).Take(pos), (xs).Drop((pos) + (BigInteger.One)));
    }
    public static Dafny.ISequence<__T> RemoveValue<__T>(Dafny.ISequence<__T> xs, __T v)
    {
      if (!(xs).Contains(v)) {
        return xs;
      } else {
        BigInteger _0_i = Std.Collections.Seq.__default.IndexOf<__T>(xs, v);
        return Dafny.Sequence<__T>.Concat((xs).Take(_0_i), (xs).Drop((_0_i) + (BigInteger.One)));
      }
    }
    public static Dafny.ISequence<__T> Insert<__T>(Dafny.ISequence<__T> xs, __T a, BigInteger pos)
    {
      return Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.Concat((xs).Take(pos), Dafny.Sequence<__T>.FromElements(a)), (xs).Drop(pos));
    }
    public static Dafny.ISequence<__T> Reverse<__T>(Dafny.ISequence<__T> xs) {
      Dafny.ISequence<__T> _0___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((xs).Equals(Dafny.Sequence<__T>.FromElements())) {
        return Dafny.Sequence<__T>.Concat(_0___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<__T>.Concat(_0___accumulator, Dafny.Sequence<__T>.FromElements((xs).Select((new BigInteger((xs).Count)) - (BigInteger.One))));
        Dafny.ISequence<__T> _in0 = (xs).Subsequence(BigInteger.Zero, (new BigInteger((xs).Count)) - (BigInteger.One));
        xs = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> Repeat<__T>(__T v, BigInteger length)
    {
      Dafny.ISequence<__T> _0___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((length).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_0___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<__T>.Concat(_0___accumulator, Dafny.Sequence<__T>.FromElements(v));
        __T _in0 = v;
        BigInteger _in1 = (length) - (BigInteger.One);
        v = _in0;
        length = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static _System._ITuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>> Unzip<__A, __B>(Dafny.ISequence<_System._ITuple2<__A, __B>> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>>.create(Dafny.Sequence<__A>.FromElements(), Dafny.Sequence<__B>.FromElements());
      } else {
        _System._ITuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>> _let_tmp_rhs0 = Std.Collections.Seq.__default.Unzip<__A, __B>(Std.Collections.Seq.__default.DropLast<_System._ITuple2<__A, __B>>(xs));
        Dafny.ISequence<__A> _0_a = _let_tmp_rhs0.dtor__0;
        Dafny.ISequence<__B> _1_b = _let_tmp_rhs0.dtor__1;
        return _System.Tuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>>.create(Dafny.Sequence<__A>.Concat(_0_a, Dafny.Sequence<__A>.FromElements((Std.Collections.Seq.__default.Last<_System._ITuple2<__A, __B>>(xs)).dtor__0)), Dafny.Sequence<__B>.Concat(_1_b, Dafny.Sequence<__B>.FromElements((Std.Collections.Seq.__default.Last<_System._ITuple2<__A, __B>>(xs)).dtor__1)));
      }
    }
    public static Dafny.ISequence<_System._ITuple2<__A, __B>> Zip<__A, __B>(Dafny.ISequence<__A> xs, Dafny.ISequence<__B> ys)
    {
      Dafny.ISequence<_System._ITuple2<__A, __B>> _0___accumulator = Dafny.Sequence<_System._ITuple2<__A, __B>>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<_System._ITuple2<__A, __B>>.Concat(Dafny.Sequence<_System._ITuple2<__A, __B>>.FromElements(), _0___accumulator);
      } else {
        _0___accumulator = Dafny.Sequence<_System._ITuple2<__A, __B>>.Concat(Dafny.Sequence<_System._ITuple2<__A, __B>>.FromElements(_System.Tuple2<__A, __B>.create(Std.Collections.Seq.__default.Last<__A>(xs), Std.Collections.Seq.__default.Last<__B>(ys))), _0___accumulator);
        Dafny.ISequence<__A> _in0 = Std.Collections.Seq.__default.DropLast<__A>(xs);
        Dafny.ISequence<__B> _in1 = Std.Collections.Seq.__default.DropLast<__B>(ys);
        xs = _in0;
        ys = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static __T MaxBy<__T>(Dafny.ISequence<__T> s, Func<__T, __T, bool> lessThan)
    {
      return Std.Collections.Seq.__default.MaxByHelper<__T>(s, BigInteger.One, (s).Select(BigInteger.Zero), lessThan);
    }
    public static __T MaxByHelper<__T>(Dafny.ISequence<__T> s, BigInteger idx, __T current, Func<__T, __T, bool> lessThan)
    {
    TAIL_CALL_START: ;
      if ((idx) == (new BigInteger((s).Count))) {
        return current;
      } else {
        __T _0_next = ((Dafny.Helpers.Id<Func<__T, __T, bool>>(lessThan)(current, (s).Select(idx))) ? ((s).Select(idx)) : (current));
        Dafny.ISequence<__T> _in0 = s;
        BigInteger _in1 = (idx) + (BigInteger.One);
        __T _in2 = _0_next;
        Func<__T, __T, bool> _in3 = lessThan;
        s = _in0;
        idx = _in1;
        current = _in2;
        lessThan = _in3;
        goto TAIL_CALL_START;
      }
    }
    public static __T MinBy<__T>(Dafny.ISequence<__T> s, Func<__T, __T, bool> lessThan)
    {
      return Std.Collections.Seq.__default.MinByHelper<__T>(s, BigInteger.One, (s).Select(BigInteger.Zero), lessThan);
    }
    public static __T MinByHelper<__T>(Dafny.ISequence<__T> s, BigInteger idx, __T current, Func<__T, __T, bool> lessThan)
    {
    TAIL_CALL_START: ;
      if ((idx) == (new BigInteger((s).Count))) {
        return current;
      } else {
        __T _0_next = ((Dafny.Helpers.Id<Func<__T, __T, bool>>(lessThan)((s).Select(idx), current)) ? ((s).Select(idx)) : (current));
        Dafny.ISequence<__T> _in0 = s;
        BigInteger _in1 = (idx) + (BigInteger.One);
        __T _in2 = _0_next;
        Func<__T, __T, bool> _in3 = lessThan;
        s = _in0;
        idx = _in1;
        current = _in2;
        lessThan = _in3;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger Max(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)) == (BigInteger.One)) {
        return (xs).Select(BigInteger.Zero);
      } else {
        return Std.Math.__default.Max((xs).Select(BigInteger.Zero), Std.Collections.Seq.__default.Max((xs).Drop(BigInteger.One)));
      }
    }
    public static BigInteger Min(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)) == (BigInteger.One)) {
        return (xs).Select(BigInteger.Zero);
      } else {
        return Std.Math.__default.Min((xs).Select(BigInteger.Zero), Std.Collections.Seq.__default.Min((xs).Drop(BigInteger.One)));
      }
    }
    public static Dafny.ISequence<__T> Flatten<__T>(Dafny.ISequence<Dafny.ISequence<__T>> xs) {
      Dafny.ISequence<__T> _0___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_0___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<__T>.Concat(_0___accumulator, (xs).Select(BigInteger.Zero));
        Dafny.ISequence<Dafny.ISequence<__T>> _in0 = (xs).Drop(BigInteger.One);
        xs = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> FlattenReverse<__T>(Dafny.ISequence<Dafny.ISequence<__T>> xs) {
      Dafny.ISequence<__T> _0___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(), _0___accumulator);
      } else {
        _0___accumulator = Dafny.Sequence<__T>.Concat(Std.Collections.Seq.__default.Last<Dafny.ISequence<__T>>(xs), _0___accumulator);
        Dafny.ISequence<Dafny.ISequence<__T>> _in0 = Std.Collections.Seq.__default.DropLast<Dafny.ISequence<__T>>(xs);
        xs = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> Join<__T>(Dafny.ISequence<Dafny.ISequence<__T>> seqs, Dafny.ISequence<__T> separator)
    {
      Dafny.ISequence<__T> _0___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((seqs).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_0___accumulator, Dafny.Sequence<__T>.FromElements());
      } else if ((new BigInteger((seqs).Count)) == (BigInteger.One)) {
        return Dafny.Sequence<__T>.Concat(_0___accumulator, (seqs).Select(BigInteger.Zero));
      } else {
        _0___accumulator = Dafny.Sequence<__T>.Concat(_0___accumulator, Dafny.Sequence<__T>.Concat((seqs).Select(BigInteger.Zero), separator));
        Dafny.ISequence<Dafny.ISequence<__T>> _in0 = (seqs).Drop(BigInteger.One);
        Dafny.ISequence<__T> _in1 = separator;
        seqs = _in0;
        separator = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.ISequence<__T>> Split<__T>(Dafny.ISequence<__T> s, __T delim)
    {
      Dafny.ISequence<Dafny.ISequence<__T>> _0___accumulator = Dafny.Sequence<Dafny.ISequence<__T>>.FromElements();
    TAIL_CALL_START: ;
      Std.Wrappers._IOption<BigInteger> _1_i = Std.Collections.Seq.__default.IndexOfOption<__T>(s, delim);
      if ((_1_i).is_Some) {
        _0___accumulator = Dafny.Sequence<Dafny.ISequence<__T>>.Concat(_0___accumulator, Dafny.Sequence<Dafny.ISequence<__T>>.FromElements((s).Take((_1_i).dtor_value)));
        Dafny.ISequence<__T> _in0 = (s).Drop(((_1_i).dtor_value) + (BigInteger.One));
        __T _in1 = delim;
        s = _in0;
        delim = _in1;
        goto TAIL_CALL_START;
      } else {
        return Dafny.Sequence<Dafny.ISequence<__T>>.Concat(_0___accumulator, Dafny.Sequence<Dafny.ISequence<__T>>.FromElements(s));
      }
    }
    public static _System._ITuple2<Dafny.ISequence<__T>, Dafny.ISequence<__T>> SplitOnce<__T>(Dafny.ISequence<__T> s, __T delim)
    {
      Std.Wrappers._IOption<BigInteger> _0_i = Std.Collections.Seq.__default.IndexOfOption<__T>(s, delim);
      return _System.Tuple2<Dafny.ISequence<__T>, Dafny.ISequence<__T>>.create((s).Take((_0_i).dtor_value), (s).Drop(((_0_i).dtor_value) + (BigInteger.One)));
    }
    public static Std.Wrappers._IOption<_System._ITuple2<Dafny.ISequence<__T>, Dafny.ISequence<__T>>> SplitOnceOption<__T>(Dafny.ISequence<__T> s, __T delim)
    {
      Std.Wrappers._IOption<BigInteger> _0_valueOrError0 = Std.Collections.Seq.__default.IndexOfOption<__T>(s, delim);
      if ((_0_valueOrError0).IsFailure()) {
        return (_0_valueOrError0).PropagateFailure<_System._ITuple2<Dafny.ISequence<__T>, Dafny.ISequence<__T>>>();
      } else {
        BigInteger _1_i = (_0_valueOrError0).Extract();
        return Std.Wrappers.Option<_System._ITuple2<Dafny.ISequence<__T>, Dafny.ISequence<__T>>>.create_Some(_System.Tuple2<Dafny.ISequence<__T>, Dafny.ISequence<__T>>.create((s).Take(_1_i), (s).Drop((_1_i) + (BigInteger.One))));
      }
    }
    public static Dafny.ISequence<__R> Map<__T, __R>(Func<__T, __R> f, Dafny.ISequence<__T> xs)
    {
      Dafny.ISequence<__R> _0___accumulator = Dafny.Sequence<__R>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<__R>.Concat(_0___accumulator, Dafny.Sequence<__R>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<__R>.Concat(_0___accumulator, Dafny.Sequence<__R>.FromElements(Dafny.Helpers.Id<Func<__T, __R>>(f)((xs).Select(BigInteger.Zero))));
        Func<__T, __R> _in0 = f;
        Dafny.ISequence<__T> _in1 = (xs).Drop(BigInteger.One);
        f = _in0;
        xs = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__R> MapPartialFunction<__T, __R>(Func<__T, __R> f, Dafny.ISequence<__T> xs)
    {
      return Std.Collections.Seq.__default.Map<__T, __R>(f, xs);
    }
    public static Std.Wrappers._IResult<Dafny.ISequence<__R>, __E> MapWithResult<__T, __R, __E>(Func<__T, Std.Wrappers._IResult<__R, __E>> f, Dafny.ISequence<__T> xs)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Std.Wrappers.Result<Dafny.ISequence<__R>, __E>.create_Success(Dafny.Sequence<__R>.FromElements());
      } else {
        Std.Wrappers._IResult<__R, __E> _0_valueOrError0 = Dafny.Helpers.Id<Func<__T, Std.Wrappers._IResult<__R, __E>>>(f)((xs).Select(BigInteger.Zero));
        if ((_0_valueOrError0).IsFailure()) {
          return (_0_valueOrError0).PropagateFailure<Dafny.ISequence<__R>>();
        } else {
          __R _1_head = (_0_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__R>, __E> _2_valueOrError1 = Std.Collections.Seq.__default.MapWithResult<__T, __R, __E>(f, (xs).Drop(BigInteger.One));
          if ((_2_valueOrError1).IsFailure()) {
            return (_2_valueOrError1).PropagateFailure<Dafny.ISequence<__R>>();
          } else {
            Dafny.ISequence<__R> _3_tail = (_2_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__R>, __E>.create_Success(Dafny.Sequence<__R>.Concat(Dafny.Sequence<__R>.FromElements(_1_head), _3_tail));
          }
        }
      }
    }
    public static Dafny.ISequence<__T> Filter<__T>(Func<__T, bool> f, Dafny.ISequence<__T> xs)
    {
      Dafny.ISequence<__T> _0___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_0___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<__T>.Concat(_0___accumulator, ((Dafny.Helpers.Id<Func<__T, bool>>(f)((xs).Select(BigInteger.Zero))) ? (Dafny.Sequence<__T>.FromElements((xs).Select(BigInteger.Zero))) : (Dafny.Sequence<__T>.FromElements())));
        Func<__T, bool> _in0 = f;
        Dafny.ISequence<__T> _in1 = (xs).Drop(BigInteger.One);
        f = _in0;
        xs = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static __A FoldLeft<__A, __T>(Func<__A, __T, __A> f, __A init, Dafny.ISequence<__T> xs)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return init;
      } else {
        Func<__A, __T, __A> _in0 = f;
        __A _in1 = Dafny.Helpers.Id<Func<__A, __T, __A>>(f)(init, (xs).Select(BigInteger.Zero));
        Dafny.ISequence<__T> _in2 = (xs).Drop(BigInteger.One);
        f = _in0;
        init = _in1;
        xs = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static __A FoldRight<__A, __T>(Func<__T, __A, __A> f, Dafny.ISequence<__T> xs, __A init)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return init;
      } else {
        return Dafny.Helpers.Id<Func<__T, __A, __A>>(f)((xs).Select(BigInteger.Zero), Std.Collections.Seq.__default.FoldRight<__A, __T>(f, (xs).Drop(BigInteger.One), init));
      }
    }
    public static Dafny.ISequence<__T> MergeSortBy<__T>(Func<__T, __T, bool> lessThanOrEq, Dafny.ISequence<__T> a)
    {
      if ((new BigInteger((a).Count)) <= (BigInteger.One)) {
        return a;
      } else {
        BigInteger _0_splitIndex = Dafny.Helpers.EuclideanDivision(new BigInteger((a).Count), new BigInteger(2));
        Dafny.ISequence<__T> _1_left = (a).Take(_0_splitIndex);
        Dafny.ISequence<__T> _2_right = (a).Drop(_0_splitIndex);
        Dafny.ISequence<__T> _3_leftSorted = Std.Collections.Seq.__default.MergeSortBy<__T>(lessThanOrEq, _1_left);
        Dafny.ISequence<__T> _4_rightSorted = Std.Collections.Seq.__default.MergeSortBy<__T>(lessThanOrEq, _2_right);
        return Std.Collections.Seq.__default.MergeSortedWith<__T>(_3_leftSorted, _4_rightSorted, lessThanOrEq);
      }
    }
    public static Dafny.ISequence<__T> MergeSortedWith<__T>(Dafny.ISequence<__T> left, Dafny.ISequence<__T> right, Func<__T, __T, bool> lessThanOrEq)
    {
      Dafny.ISequence<__T> _0___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((left).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_0___accumulator, right);
      } else if ((new BigInteger((right).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_0___accumulator, left);
      } else if (Dafny.Helpers.Id<Func<__T, __T, bool>>(lessThanOrEq)((left).Select(BigInteger.Zero), (right).Select(BigInteger.Zero))) {
        _0___accumulator = Dafny.Sequence<__T>.Concat(_0___accumulator, Dafny.Sequence<__T>.FromElements((left).Select(BigInteger.Zero)));
        Dafny.ISequence<__T> _in0 = (left).Drop(BigInteger.One);
        Dafny.ISequence<__T> _in1 = right;
        Func<__T, __T, bool> _in2 = lessThanOrEq;
        left = _in0;
        right = _in1;
        lessThanOrEq = _in2;
        goto TAIL_CALL_START;
      } else {
        _0___accumulator = Dafny.Sequence<__T>.Concat(_0___accumulator, Dafny.Sequence<__T>.FromElements((right).Select(BigInteger.Zero)));
        Dafny.ISequence<__T> _in3 = left;
        Dafny.ISequence<__T> _in4 = (right).Drop(BigInteger.One);
        Func<__T, __T, bool> _in5 = lessThanOrEq;
        left = _in3;
        right = _in4;
        lessThanOrEq = _in5;
        goto TAIL_CALL_START;
      }
    }
    public static bool All<__T>(Dafny.ISequence<__T> s, Func<__T, bool> p)
    {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Func<__T, bool>, bool>>((_0_s, _1_p) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_0_s).Count)), true, (((_forall_var_0) => {
        BigInteger _2_i = (BigInteger)_forall_var_0;
        return !(((_2_i).Sign != -1) && ((_2_i) < (new BigInteger((_0_s).Count)))) || (Dafny.Helpers.Id<Func<__T, bool>>(_1_p)((_0_s).Select(_2_i)));
      }))))(s, p);
    }
    public static bool AllNot<__T>(Dafny.ISequence<__T> s, Func<__T, bool> p)
    {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Func<__T, bool>, bool>>((_0_s, _1_p) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_0_s).Count)), true, (((_forall_var_0) => {
        BigInteger _2_i = (BigInteger)_forall_var_0;
        return !(((_2_i).Sign != -1) && ((_2_i) < (new BigInteger((_0_s).Count)))) || (!(Dafny.Helpers.Id<Func<__T, bool>>(_1_p)((_0_s).Select(_2_i))));
      }))))(s, p);
    }
    public static bool Partitioned<__T>(Dafny.ISequence<__T> s, Func<__T, bool> p)
    {
    TAIL_CALL_START: ;
      if ((s).Equals(Dafny.Sequence<__T>.FromElements())) {
        return true;
      } else if (Dafny.Helpers.Id<Func<__T, bool>>(p)((s).Select(BigInteger.Zero))) {
        Dafny.ISequence<__T> _in0 = (s).Drop(BigInteger.One);
        Func<__T, bool> _in1 = p;
        s = _in0;
        p = _in1;
        goto TAIL_CALL_START;
      } else {
        return Std.Collections.Seq.__default.AllNot<__T>((s).Drop(BigInteger.One), p);
      }
    }
  }

  public interface _ISlice<T> {
    bool is_Slice { get; }
    Dafny.ISequence<T> dtor_data { get; }
    BigInteger dtor_start { get; }
    BigInteger dtor_end { get; }
    _ISlice<__T> DowncastClone<__T>(Func<T, __T> converter0);
    Dafny.ISequence<T> View();
    BigInteger Length();
    T At(BigInteger i);
    Std.Collections.Seq._ISlice<T> Drop(BigInteger firstIncludedIndex);
    Std.Collections.Seq._ISlice<T> Sub(BigInteger firstIncludedIndex, BigInteger lastExcludedIndex);
  }
  public class Slice<T> : _ISlice<T> {
    public readonly Dafny.ISequence<T> _data;
    public readonly BigInteger _start;
    public readonly BigInteger _end;
    public Slice(Dafny.ISequence<T> data, BigInteger start, BigInteger end) {
      this._data = data;
      this._start = start;
      this._end = end;
    }
    public _ISlice<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _ISlice<__T> dt) { return dt; }
      return new Slice<__T>((_data).DowncastClone<__T>(Dafny.Helpers.CastConverter<T, __T>), _start, _end);
    }
    public override bool Equals(object other) {
      var oth = other as Std.Collections.Seq.Slice<T>;
      return oth != null && object.Equals(this._data, oth._data) && this._start == oth._start && this._end == oth._end;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._data));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._start));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._end));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Seq.Slice.Slice";
      s += "(";
      s += Dafny.Helpers.ToString(this._data);
      s += ", ";
      s += Dafny.Helpers.ToString(this._start);
      s += ", ";
      s += Dafny.Helpers.ToString(this._end);
      s += ")";
      return s;
    }
    public static Std.Collections.Seq._ISlice<T> Default() {
      return create(Dafny.Sequence<T>.Empty, BigInteger.Zero, BigInteger.Zero);
    }
    public static Dafny.TypeDescriptor<Std.Collections.Seq._ISlice<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Std.Collections.Seq._ISlice<T>>(Std.Collections.Seq.Slice<T>.Default());
    }
    public static _ISlice<T> create(Dafny.ISequence<T> data, BigInteger start, BigInteger end) {
      return new Slice<T>(data, start, end);
    }
    public static _ISlice<T> create_Slice(Dafny.ISequence<T> data, BigInteger start, BigInteger end) {
      return create(data, start, end);
    }
    public bool is_Slice { get { return true; } }
    public Dafny.ISequence<T> dtor_data {
      get {
        return this._data;
      }
    }
    public BigInteger dtor_start {
      get {
        return this._start;
      }
    }
    public BigInteger dtor_end {
      get {
        return this._end;
      }
    }
    public Dafny.ISequence<T> View() {
      return ((this).dtor_data).Subsequence((this).dtor_start, (this).dtor_end);
    }
    public BigInteger Length() {
      return ((this).dtor_end) - ((this).dtor_start);
    }
    public T At(BigInteger i) {
      return ((this).dtor_data).Select(((this).dtor_start) + (i));
    }
    public Std.Collections.Seq._ISlice<T> Drop(BigInteger firstIncludedIndex) {
      return Std.Collections.Seq.Slice<T>.create((this).dtor_data, ((this).dtor_start) + (firstIncludedIndex), (this).dtor_end);
    }
    public Std.Collections.Seq._ISlice<T> Sub(BigInteger firstIncludedIndex, BigInteger lastExcludedIndex)
    {
      return Std.Collections.Seq.Slice<T>.create((this).dtor_data, ((this).dtor_start) + (firstIncludedIndex), ((this).dtor_start) + (lastExcludedIndex));
    }
  }
} // end of namespace Std.Collections.Seq