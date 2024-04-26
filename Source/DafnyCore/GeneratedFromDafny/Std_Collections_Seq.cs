// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;

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
      Func<BigInteger, __T> _init2 = Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Func<BigInteger, __T>>>((_83_xs) => ((System.Func<BigInteger, __T>)((_84_i) => {
        return (_83_xs).Select(_84_i);
      })))(xs);
      __T[] _nw3 = new __T[Dafny.Helpers.ToIntChecked(new BigInteger((xs).Count), "array size exceeds memory limit")];
      for (var _i0_2 = 0; _i0_2 < new BigInteger(_nw3.Length); _i0_2++) {
        _nw3[(int)(_i0_2)] = _init2(_i0_2);
      }
      a = _nw3;
      return a;
    }
    public static Dafny.ISet<__T> ToSet<__T>(Dafny.ISequence<__T> xs) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Dafny.ISet<__T>>>((_85_xs) => ((System.Func<Dafny.ISet<__T>>)(() => {
        var _coll0 = new System.Collections.Generic.List<__T>();
        foreach (__T _compr_0 in (_85_xs).CloneAsArray()) {
          __T _86_x = (__T)_compr_0;
          if ((_85_xs).Contains(_86_x)) {
            _coll0.Add(_86_x);
          }
        }
        return Dafny.Set<__T>.FromCollection(_coll0);
      }))())(xs);
    }
    public static BigInteger IndexOf<__T>(Dafny.ISequence<__T> xs, __T v)
    {
      BigInteger _87___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if (object.Equals((xs).Select(BigInteger.Zero), v)) {
        return (BigInteger.Zero) + (_87___accumulator);
      } else {
        _87___accumulator = (_87___accumulator) + (BigInteger.One);
        Dafny.ISequence<__T> _in0 = (xs).Drop(BigInteger.One);
        __T _in1 = v;
        xs = _in0;
        v = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Std.Wrappers._IOption<BigInteger> IndexOfOption<__T>(Dafny.ISequence<__T> xs, __T v)
    {
      return Std.Collections.Seq.__default.IndexByOption<__T>(xs, Dafny.Helpers.Id<Func<__T, Func<__T, bool>>>((_88_v) => ((System.Func<__T, bool>)((_89_x) => {
        return object.Equals(_89_x, _88_v);
      })))(v));
    }
    public static Std.Wrappers._IOption<BigInteger> IndexByOption<__T>(Dafny.ISequence<__T> xs, Func<__T, bool> p)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Std.Wrappers.Option<BigInteger>.create_None();
      } else if (Dafny.Helpers.Id<Func<__T, bool>>(p)((xs).Select(BigInteger.Zero))) {
        return Std.Wrappers.Option<BigInteger>.create_Some(BigInteger.Zero);
      } else {
        Std.Wrappers._IOption<BigInteger> _90_o_k = Std.Collections.Seq.__default.IndexByOption<__T>((xs).Drop(BigInteger.One), p);
        if ((_90_o_k).is_Some) {
          return Std.Wrappers.Option<BigInteger>.create_Some(((_90_o_k).dtor_value) + (BigInteger.One));
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
        Dafny.ISequence<__T> _in2 = (xs).Take((new BigInteger((xs).Count)) - (BigInteger.One));
        __T _in3 = v;
        xs = _in2;
        v = _in3;
        goto TAIL_CALL_START;
      }
    }
    public static Std.Wrappers._IOption<BigInteger> LastIndexOfOption<__T>(Dafny.ISequence<__T> xs, __T v)
    {
      return Std.Collections.Seq.__default.LastIndexByOption<__T>(xs, Dafny.Helpers.Id<Func<__T, Func<__T, bool>>>((_91_v) => ((System.Func<__T, bool>)((_92_x) => {
        return object.Equals(_92_x, _91_v);
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
        Dafny.ISequence<__T> _in4 = (xs).Take((new BigInteger((xs).Count)) - (BigInteger.One));
        Func<__T, bool> _in5 = p;
        xs = _in4;
        p = _in5;
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
        BigInteger _93_i = Std.Collections.Seq.__default.IndexOf<__T>(xs, v);
        return Dafny.Sequence<__T>.Concat((xs).Take(_93_i), (xs).Drop((_93_i) + (BigInteger.One)));
      }
    }
    public static Dafny.ISequence<__T> Insert<__T>(Dafny.ISequence<__T> xs, __T a, BigInteger pos)
    {
      return Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.Concat((xs).Take(pos), Dafny.Sequence<__T>.FromElements(a)), (xs).Drop(pos));
    }
    public static Dafny.ISequence<__T> Reverse<__T>(Dafny.ISequence<__T> xs) {
      Dafny.ISequence<__T> _94___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((xs).Equals(Dafny.Sequence<__T>.FromElements())) {
        return Dafny.Sequence<__T>.Concat(_94___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _94___accumulator = Dafny.Sequence<__T>.Concat(_94___accumulator, Dafny.Sequence<__T>.FromElements((xs).Select((new BigInteger((xs).Count)) - (BigInteger.One))));
        Dafny.ISequence<__T> _in6 = (xs).Subsequence(BigInteger.Zero, (new BigInteger((xs).Count)) - (BigInteger.One));
        xs = _in6;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> Repeat<__T>(__T v, BigInteger length)
    {
      Dafny.ISequence<__T> _95___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((length).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_95___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _95___accumulator = Dafny.Sequence<__T>.Concat(_95___accumulator, Dafny.Sequence<__T>.FromElements(v));
        __T _in7 = v;
        BigInteger _in8 = (length) - (BigInteger.One);
        v = _in7;
        length = _in8;
        goto TAIL_CALL_START;
      }
    }
    public static _System._ITuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>> Unzip<__A, __B>(Dafny.ISequence<_System._ITuple2<__A, __B>> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>>.create(Dafny.Sequence<__A>.FromElements(), Dafny.Sequence<__B>.FromElements());
      } else {
        _System._ITuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>> _let_tmp_rhs0 = Std.Collections.Seq.__default.Unzip<__A, __B>(Std.Collections.Seq.__default.DropLast<_System._ITuple2<__A, __B>>(xs));
        Dafny.ISequence<__A> _96_a = _let_tmp_rhs0.dtor__0;
        Dafny.ISequence<__B> _97_b = _let_tmp_rhs0.dtor__1;
        return _System.Tuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>>.create(Dafny.Sequence<__A>.Concat(_96_a, Dafny.Sequence<__A>.FromElements((Std.Collections.Seq.__default.Last<_System._ITuple2<__A, __B>>(xs)).dtor__0)), Dafny.Sequence<__B>.Concat(_97_b, Dafny.Sequence<__B>.FromElements((Std.Collections.Seq.__default.Last<_System._ITuple2<__A, __B>>(xs)).dtor__1)));
      }
    }
    public static Dafny.ISequence<_System._ITuple2<__A, __B>> Zip<__A, __B>(Dafny.ISequence<__A> xs, Dafny.ISequence<__B> ys)
    {
      Dafny.ISequence<_System._ITuple2<__A, __B>> _98___accumulator = Dafny.Sequence<_System._ITuple2<__A, __B>>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<_System._ITuple2<__A, __B>>.Concat(Dafny.Sequence<_System._ITuple2<__A, __B>>.FromElements(), _98___accumulator);
      } else {
        _98___accumulator = Dafny.Sequence<_System._ITuple2<__A, __B>>.Concat(Dafny.Sequence<_System._ITuple2<__A, __B>>.FromElements(_System.Tuple2<__A, __B>.create(Std.Collections.Seq.__default.Last<__A>(xs), Std.Collections.Seq.__default.Last<__B>(ys))), _98___accumulator);
        Dafny.ISequence<__A> _in9 = Std.Collections.Seq.__default.DropLast<__A>(xs);
        Dafny.ISequence<__B> _in10 = Std.Collections.Seq.__default.DropLast<__B>(ys);
        xs = _in9;
        ys = _in10;
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
      Dafny.ISequence<__T> _99___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_99___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _99___accumulator = Dafny.Sequence<__T>.Concat(_99___accumulator, (xs).Select(BigInteger.Zero));
        Dafny.ISequence<Dafny.ISequence<__T>> _in11 = (xs).Drop(BigInteger.One);
        xs = _in11;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> FlattenReverse<__T>(Dafny.ISequence<Dafny.ISequence<__T>> xs) {
      Dafny.ISequence<__T> _100___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(), _100___accumulator);
      } else {
        _100___accumulator = Dafny.Sequence<__T>.Concat(Std.Collections.Seq.__default.Last<Dafny.ISequence<__T>>(xs), _100___accumulator);
        Dafny.ISequence<Dafny.ISequence<__T>> _in12 = Std.Collections.Seq.__default.DropLast<Dafny.ISequence<__T>>(xs);
        xs = _in12;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> Join<__T>(Dafny.ISequence<Dafny.ISequence<__T>> seqs, Dafny.ISequence<__T> separator)
    {
      Dafny.ISequence<__T> _101___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((seqs).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_101___accumulator, Dafny.Sequence<__T>.FromElements());
      } else if ((new BigInteger((seqs).Count)) == (BigInteger.One)) {
        return Dafny.Sequence<__T>.Concat(_101___accumulator, (seqs).Select(BigInteger.Zero));
      } else {
        _101___accumulator = Dafny.Sequence<__T>.Concat(_101___accumulator, Dafny.Sequence<__T>.Concat((seqs).Select(BigInteger.Zero), separator));
        Dafny.ISequence<Dafny.ISequence<__T>> _in13 = (seqs).Drop(BigInteger.One);
        Dafny.ISequence<__T> _in14 = separator;
        seqs = _in13;
        separator = _in14;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.ISequence<__T>> Split<__T>(Dafny.ISequence<__T> s, __T delim)
    {
      Dafny.ISequence<Dafny.ISequence<__T>> _102___accumulator = Dafny.Sequence<Dafny.ISequence<__T>>.FromElements();
    TAIL_CALL_START: ;
      Std.Wrappers._IOption<BigInteger> _103_i = Std.Collections.Seq.__default.IndexOfOption<__T>(s, delim);
      if ((_103_i).is_Some) {
        _102___accumulator = Dafny.Sequence<Dafny.ISequence<__T>>.Concat(_102___accumulator, Dafny.Sequence<Dafny.ISequence<__T>>.FromElements((s).Take((_103_i).dtor_value)));
        Dafny.ISequence<__T> _in15 = (s).Drop(((_103_i).dtor_value) + (BigInteger.One));
        __T _in16 = delim;
        s = _in15;
        delim = _in16;
        goto TAIL_CALL_START;
      } else {
        return Dafny.Sequence<Dafny.ISequence<__T>>.Concat(_102___accumulator, Dafny.Sequence<Dafny.ISequence<__T>>.FromElements(s));
      }
    }
    public static _System._ITuple2<Dafny.ISequence<__T>, Dafny.ISequence<__T>> SplitOnce<__T>(Dafny.ISequence<__T> s, __T delim)
    {
      Std.Wrappers._IOption<BigInteger> _104_i = Std.Collections.Seq.__default.IndexOfOption<__T>(s, delim);
      return _System.Tuple2<Dafny.ISequence<__T>, Dafny.ISequence<__T>>.create((s).Take((_104_i).dtor_value), (s).Drop(((_104_i).dtor_value) + (BigInteger.One)));
    }
    public static Std.Wrappers._IOption<_System._ITuple2<Dafny.ISequence<__T>, Dafny.ISequence<__T>>> SplitOnceOption<__T>(Dafny.ISequence<__T> s, __T delim)
    {
      Std.Wrappers._IOption<BigInteger> _105_valueOrError0 = Std.Collections.Seq.__default.IndexOfOption<__T>(s, delim);
      if ((_105_valueOrError0).IsFailure()) {
        return (_105_valueOrError0).PropagateFailure<_System._ITuple2<Dafny.ISequence<__T>, Dafny.ISequence<__T>>>();
      } else {
        BigInteger _106_i = (_105_valueOrError0).Extract();
        return Std.Wrappers.Option<_System._ITuple2<Dafny.ISequence<__T>, Dafny.ISequence<__T>>>.create_Some(_System.Tuple2<Dafny.ISequence<__T>, Dafny.ISequence<__T>>.create((s).Take(_106_i), (s).Drop((_106_i) + (BigInteger.One))));
      }
    }
    public static Dafny.ISequence<__R> Map<__T, __R>(Func<__T, __R> f, Dafny.ISequence<__T> xs)
    {
      Dafny.ISequence<__R> _107___accumulator = Dafny.Sequence<__R>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<__R>.Concat(_107___accumulator, Dafny.Sequence<__R>.FromElements());
      } else {
        _107___accumulator = Dafny.Sequence<__R>.Concat(_107___accumulator, Dafny.Sequence<__R>.FromElements(Dafny.Helpers.Id<Func<__T, __R>>(f)((xs).Select(BigInteger.Zero))));
        Func<__T, __R> _in17 = f;
        Dafny.ISequence<__T> _in18 = (xs).Drop(BigInteger.One);
        f = _in17;
        xs = _in18;
        goto TAIL_CALL_START;
      }
    }
    public static Std.Wrappers._IResult<Dafny.ISequence<__R>, __E> MapWithResult<__T, __R, __E>(Func<__T, Std.Wrappers._IResult<__R, __E>> f, Dafny.ISequence<__T> xs)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Std.Wrappers.Result<Dafny.ISequence<__R>, __E>.create_Success(Dafny.Sequence<__R>.FromElements());
      } else {
        Std.Wrappers._IResult<__R, __E> _108_valueOrError0 = Dafny.Helpers.Id<Func<__T, Std.Wrappers._IResult<__R, __E>>>(f)((xs).Select(BigInteger.Zero));
        if ((_108_valueOrError0).IsFailure()) {
          return (_108_valueOrError0).PropagateFailure<Dafny.ISequence<__R>>();
        } else {
          __R _109_head = (_108_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__R>, __E> _110_valueOrError1 = Std.Collections.Seq.__default.MapWithResult<__T, __R, __E>(f, (xs).Drop(BigInteger.One));
          if ((_110_valueOrError1).IsFailure()) {
            return (_110_valueOrError1).PropagateFailure<Dafny.ISequence<__R>>();
          } else {
            Dafny.ISequence<__R> _111_tail = (_110_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__R>, __E>.create_Success(Dafny.Sequence<__R>.Concat(Dafny.Sequence<__R>.FromElements(_109_head), _111_tail));
          }
        }
      }
    }
    public static Dafny.ISequence<__T> Filter<__T>(Func<__T, bool> f, Dafny.ISequence<__T> xs)
    {
      Dafny.ISequence<__T> _112___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_112___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _112___accumulator = Dafny.Sequence<__T>.Concat(_112___accumulator, ((Dafny.Helpers.Id<Func<__T, bool>>(f)((xs).Select(BigInteger.Zero))) ? (Dafny.Sequence<__T>.FromElements((xs).Select(BigInteger.Zero))) : (Dafny.Sequence<__T>.FromElements())));
        Func<__T, bool> _in19 = f;
        Dafny.ISequence<__T> _in20 = (xs).Drop(BigInteger.One);
        f = _in19;
        xs = _in20;
        goto TAIL_CALL_START;
      }
    }
    public static __A FoldLeft<__A, __T>(Func<__A, __T, __A> f, __A init, Dafny.ISequence<__T> xs)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return init;
      } else {
        Func<__A, __T, __A> _in21 = f;
        __A _in22 = Dafny.Helpers.Id<Func<__A, __T, __A>>(f)(init, (xs).Select(BigInteger.Zero));
        Dafny.ISequence<__T> _in23 = (xs).Drop(BigInteger.One);
        f = _in21;
        init = _in22;
        xs = _in23;
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
    public static Dafny.ISequence<__T> SetToSeq<__T>(Dafny.ISet<__T> s)
    {
      Dafny.ISequence<__T> xs = Dafny.Sequence<__T>.Empty;
      xs = Dafny.Sequence<__T>.FromElements();
      Dafny.ISet<__T> _113_left;
      _113_left = s;
      while (!(_113_left).Equals(Dafny.Set<__T>.FromElements())) {
        __T _114_x;
        foreach (__T _assign_such_that_0 in (_113_left).Elements) {
          _114_x = (__T)_assign_such_that_0;
          if ((_113_left).Contains(_114_x)) {
            goto after__ASSIGN_SUCH_THAT_0;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 7247)");
      after__ASSIGN_SUCH_THAT_0: ;
        _113_left = Dafny.Set<__T>.Difference(_113_left, Dafny.Set<__T>.FromElements(_114_x));
        xs = Dafny.Sequence<__T>.Concat(xs, Dafny.Sequence<__T>.FromElements(_114_x));
      }
      return xs;
    }
    public static Dafny.ISequence<__T> SetToSortedSeq<__T>(Dafny.ISet<__T> s, Func<__T, __T, bool> R)
    {
      Dafny.ISequence<__T> xs = Dafny.Sequence<__T>.Empty;
      Dafny.ISequence<__T> _out6;
      _out6 = Std.Collections.Seq.__default.SetToSeq<__T>(s);
      xs = _out6;
      xs = Std.Collections.Seq.__default.MergeSortBy<__T>(R, xs);
      return xs;
    }
    public static Dafny.ISequence<__T> MergeSortBy<__T>(Func<__T, __T, bool> lessThanOrEq, Dafny.ISequence<__T> a)
    {
      if ((new BigInteger((a).Count)) <= (BigInteger.One)) {
        return a;
      } else {
        BigInteger _115_splitIndex = Dafny.Helpers.EuclideanDivision(new BigInteger((a).Count), new BigInteger(2));
        Dafny.ISequence<__T> _116_left = (a).Take(_115_splitIndex);
        Dafny.ISequence<__T> _117_right = (a).Drop(_115_splitIndex);
        Dafny.ISequence<__T> _118_leftSorted = Std.Collections.Seq.__default.MergeSortBy<__T>(lessThanOrEq, _116_left);
        Dafny.ISequence<__T> _119_rightSorted = Std.Collections.Seq.__default.MergeSortBy<__T>(lessThanOrEq, _117_right);
        return Std.Collections.Seq.__default.MergeSortedWith<__T>(_118_leftSorted, _119_rightSorted, lessThanOrEq);
      }
    }
    public static Dafny.ISequence<__T> MergeSortedWith<__T>(Dafny.ISequence<__T> left, Dafny.ISequence<__T> right, Func<__T, __T, bool> lessThanOrEq)
    {
      Dafny.ISequence<__T> _120___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((left).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_120___accumulator, right);
      } else if ((new BigInteger((right).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_120___accumulator, left);
      } else if (Dafny.Helpers.Id<Func<__T, __T, bool>>(lessThanOrEq)((left).Select(BigInteger.Zero), (right).Select(BigInteger.Zero))) {
        _120___accumulator = Dafny.Sequence<__T>.Concat(_120___accumulator, Dafny.Sequence<__T>.FromElements((left).Select(BigInteger.Zero)));
        Dafny.ISequence<__T> _in24 = (left).Drop(BigInteger.One);
        Dafny.ISequence<__T> _in25 = right;
        Func<__T, __T, bool> _in26 = lessThanOrEq;
        left = _in24;
        right = _in25;
        lessThanOrEq = _in26;
        goto TAIL_CALL_START;
      } else {
        _120___accumulator = Dafny.Sequence<__T>.Concat(_120___accumulator, Dafny.Sequence<__T>.FromElements((right).Select(BigInteger.Zero)));
        Dafny.ISequence<__T> _in27 = left;
        Dafny.ISequence<__T> _in28 = (right).Drop(BigInteger.One);
        Func<__T, __T, bool> _in29 = lessThanOrEq;
        left = _in27;
        right = _in28;
        lessThanOrEq = _in29;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Std.Collections.Seq