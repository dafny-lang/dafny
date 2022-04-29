module Lib {
  module Seq {
    function method {:opaque} Map<T, Q>(f: T ~> Q, ts: seq<T>) : (qs: seq<Q>)
      reads f.reads
      requires forall t | t in ts :: f.requires(t)
      ensures |qs| == |ts|
      ensures forall i | 0 <= i < |ts| :: qs[i] == f(ts[i])
    {
      if ts == [] then [] else [f(ts[0])] + Map(f, ts[1..])
    }

    function method FoldL<TAcc(!new), T>(f: (TAcc, T) ~> TAcc, a0: TAcc, ts: seq<T>) : TAcc
      reads f.reads // FIXME: what does this mean?
      requires forall a, t | t in ts :: f.requires(a, t)
    {
      if ts == [] then a0 else FoldL(f, f(a0, ts[0]), ts[1..])
    }

    lemma FoldL_induction'<TAcc(!new), T>(
      f: (TAcc, T) ~> TAcc, a0: TAcc, ts: seq<T>,
      prefix: seq<T>, P: (TAcc, seq<T>) -> bool
    )
      requires forall a, t | t in ts :: f.requires(a, t)
      requires P(a0, prefix)
      requires forall a, t, ts' | t in ts && P(a, ts') :: P(f(a, t), ts' + [t])
      ensures P(FoldL(f, a0, ts), prefix + ts)
    {
      if ts == [] {
        assert prefix + ts == prefix;
      } else {
        var t0, ts' := ts[0], ts[1..];
        var a0' := f(a0, t0);
        var prefix' := prefix + [t0];
        FoldL_induction'(f, a0', ts[1..], prefix', P);
        assert P(FoldL(f, a0', ts[1..]), prefix' + ts');
        assert prefix' + ts' == prefix + ts;
      }
    }

    lemma FoldL_induction<TAcc(!new), T>(
      f: (TAcc, T) ~> TAcc, a0: TAcc, ts: seq<T>,
      P: (TAcc, seq<T>) -> bool
    )
      requires forall a, t | t in ts :: f.requires(a, t)
      requires P(a0, [])
      requires forall a, t, ts' | t in ts && P(a, ts') :: P(f(a, t), ts' + [t])
      ensures P(FoldL(f, a0, ts), ts)
    {
      assert [] + ts == ts;
      FoldL_induction'(f, a0, ts, [], P);
    }

    function method {:opaque} All<T>(P: T ~> bool, ts: seq<T>) : (b: bool)
      reads P.reads // FIXME: what does this mean?
      requires forall t | t in ts :: P.requires(t)
      ensures b == forall t | t in ts :: P(t)
      ensures b == forall i | 0 <= i < |ts| :: P(ts[i])
    {
      if ts == [] then true else P(ts[0]) && All(P, ts[1..])
    }

    lemma All_weaken<T>(P: T ~> bool, Q: T~> bool, ts: seq<T>)
      requires forall t | t in ts :: P.requires(t)
      requires forall t | t in ts :: Q.requires(t)
      requires forall t | t in ts :: P(t) ==> Q(t)
      ensures All(P, ts) ==> All(Q, ts)
    {}

    lemma All_weaken_auto<T>(ts: seq<T>)
      ensures forall P: T ~> bool, Q: T ~> bool |
        && (forall t: T | t in ts :: P.requires(t))
        && (forall t: T | t in ts :: Q.requires(t))
        && (forall t: T | t in ts :: P(t) ==> Q(t)) ::
       All(P, ts) ==> All(Q, ts)
    {}

    import Math

    function method {:opaque} Max(s: seq<int>, default: int) : (m: int)
      requires forall i | i in s :: default <= i
      ensures if s == [] then m == default else m in s
      ensures forall i | i in s :: i <= m
      ensures default <= m
    {
      var P := (m, s) =>
        && (if s == [] then m == default else m in s)
        && (forall i | i in s :: i <= m);
      FoldL_induction(Math.Max, default, s, P);
      FoldL(Math.Max, default, s)
    }

    function method {:opaque} MaxF<T>(f: T ~> int, ts: seq<T>, default: int) : (m: int)
      reads f.reads
      requires forall t | t in ts :: f.requires(t)
      requires forall t | t in ts :: default <= f(t)
      ensures if ts == [] then m == default else exists t | t in ts :: f(t) == m
      ensures forall t | t in ts :: f(t) <= m
      ensures default <= m
    {
      var s := Map(f, ts);
      var m := Max(s, default);
      assert forall t | t in ts :: f(t) <= m by {
        forall t | t in ts ensures f(t) <= m { assert f(t) in s; }
      }
      m
    }

  }

  module Datatypes {
    datatype Option<T> =
      | Some(t: T)
      | None
    {
      function method OrElse(t: T) : T {
        if this.Some? then this.t else t
      }
    }
  }

  module Str {
    module Private {
      function method digits(n: int, base: int): (digits: seq<int>)
        requires base > 1
        requires n >= 0
        decreases n
        ensures forall d | d in digits :: 0 <= d < base
      {
        if n == 0 then
          []
        else
          assert n > 0;
          assert base > 1;
          assert n < base * n;
          assert n / base < n;
          digits(n / base, base) + [n % base]
      }

      function method string_of_digits(digits: seq<int>, chars: seq<char>) : string
        requires forall d | d in digits :: 0 <= d < |chars|
      {
        if digits == [] then ""
        else
          assert digits[0] in digits;
          assert forall d | d in digits[1..] :: d in digits;
          [chars[digits[0]]] + string_of_digits(digits[1..], chars)
      }
    }

    function method of_int_any(n: int, chars: seq<char>) : string
      requires |chars| > 1
    {
      var base := |chars|;
      if n == 0 then
        "0"
      else if n > 0 then
        Private.string_of_digits(Private.digits(n, base), chars)
      else
        "-" + Private.string_of_digits(Private.digits(-n, base), chars)
    }

    const HEX_DIGITS := [
      '0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
      'A', 'B', 'C', 'D', 'E', 'F']

    function method of_int(n: int, base: int := 10) : string
      requires 2 <= base <= 16
    {
      of_int_any(n, HEX_DIGITS[..base])
    }

    method Test() { // FIXME {:test}?
      expect of_int(0, 10) == "0";
      expect of_int(3, 10) == "3";
      expect of_int(302, 10) == "302";
      expect of_int(-3, 10) == "-3";
      expect of_int(-302, 10) == "-302";
    }

    function method of_bool(b: bool) : string {
      if b then "true" else "false"
    }

    function method of_char(c: char) : string {
      [c]
    }

    function method Join(sep: string, strs: seq<string>) : string {
      if |strs| == 0 then ""
      else if |strs| == 1 then strs[0]
      else strs[0] + sep + Join(sep, strs[1..])
    }

    function method Concat(strs: seq<string>) : string {
      Join("", strs)
    }
  }

  module Math {
    function method {:opaque} Max(x: int, y: int) : (m: int)
      ensures x <= m
      ensures y <= m
      ensures x == m || y == m
    {
      if (x <= y) then y else x
    }
  }
}
