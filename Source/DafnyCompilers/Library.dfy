module Lib {
  module Seq {
    function method {:opaque} Map<T, Q>(f: T ~> Q, ts: seq<T>) : (qs: seq<Q>)
      reads f.reads // FIXME: what does this mean?
      requires forall t | t in ts :: f.requires(t)
      ensures |qs| == |ts|
      ensures forall i | 0 <= i < |ts| :: qs[i] == f(ts[i])
    {
      if ts == [] then [] else [f(ts[0])] + Map(f, ts[1..])
    }

    function method All<T>(P: T ~> bool, ts: seq<T>) : (b: bool)
      reads P.reads // FIXME: what does this mean?
      requires forall t | t in ts :: P.requires(t)
      ensures b == forall i | 0 <= i < |ts| :: P(ts[i])
    {
      if ts == [] then true else P(ts[0]) && All(P, ts[1..])
    }
  }

  module Datatypes {
    datatype Option<T> =
      | Some(t: T)
      | None
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

    function method of_int(n: int, base: int) : string
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
  }
}
