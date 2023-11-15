/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/
/**
Implements functions to convert between (big-endian) strings and numbers.
*/
module {:options "-functionSyntax:4"} DafnyStdLibs.JSON.Utils.Str {
  import opened Wrappers
  import opened NonlinearArithmetic.Power
  import opened NonlinearArithmetic.Logarithm

  abstract module ParametricConversion {
    import opened Wrappers
    import opened NonlinearArithmetic.Mul
    import opened NonlinearArithmetic.DivMod
    import opened NonlinearArithmetic.Power
    import opened NonlinearArithmetic.Logarithm

    type Char(==)
    type String = seq<Char>

    // FIXME the design in LittleEndianNat makes BASE a module-level constant
    // instead of a function argument
    function Digits(n: nat, base: int): (digits: seq<int>)
      requires base > 1
      decreases n
      ensures n == 0 ==> |digits| == 0
      ensures n > 0 ==> |digits| == Log(base, n) + 1
      ensures forall d | d in digits :: 0 <= d < base
    {
      if n == 0 then
        assert Pow(base, 0) == 1 by { reveal Pow(); }
        []
      else
        LemmaDivPosIsPosAuto(); LemmaDivDecreasesAuto();
        var digits' := Digits(n / base, base);
        var digits := digits' + [n % base];
        assert |digits| == Log(base, n) + 1 by {
          assert |digits| == |digits'| + 1;
          if n < base {
            LemmaLog0(base, n);
            assert n / base == 0 by { LemmaBasicDiv(base); }
          } else {
            LemmaLogS(base, n);
            assert n / base > 0 by { LemmaDivNonZeroAuto(); }
          }
        }
        digits
    }

    function OfDigits(digits: seq<int>, chars: seq<Char>) : (str: String)
      requires forall d | d in digits :: 0 <= d < |chars|
      ensures forall c | c in str :: c in chars
      ensures |str| == |digits|
    {
      if digits == [] then []
      else
        assert digits[0] in digits;
        assert forall d | d in digits[1..] :: d in digits;
        [chars[digits[0]]] + OfDigits(digits[1..], chars)
    }

    function OfNat_any(n: nat, chars: seq<Char>) : (str: String)
      requires |chars| > 1
      ensures |str| == Log(|chars|, n) + 1
      ensures forall c | c in str :: c in chars
    {
      var base := |chars|;
      if n == 0 then reveal Log(); [chars[0]]
      else OfDigits(Digits(n, base), chars)
    }

    predicate NumberStr(str: String, minus: Char, is_digit: Char -> bool) {
      str != [] ==>
        && (str[0] == minus || is_digit(str[0]))
        && forall c | c in str[1..] :: is_digit(c)
    }

    function OfInt_any(n: int, chars: seq<Char>, minus: Char) : (str: String)
      requires |chars| > 1
      ensures NumberStr(str, minus, c => c in chars)
    {
      if n >= 0 then OfNat_any(n, chars)
      else [minus] + OfNat_any(-n, chars)
    }

    function {:vcs_split_on_every_assert} ToNat_any(str: String, base: nat, digits: map<Char, nat>) : (n: nat)
      requires base > 0
      requires forall c | c in str :: c in digits
    {
      if str == [] then 0
      else
        LemmaMulNonnegativeAuto();
        ToNat_any(str[..|str| - 1], base, digits) * base + digits[str[|str| - 1]]
    }

    lemma {:induction false} ToNat_bound(str: String, base: nat, digits: map<Char, nat>)
      requires base > 0
      requires forall c | c in str :: c in digits
      requires forall c | c in str :: digits[c] < base
      ensures ToNat_any(str, base, digits) < Pow(base, |str|)
    {
      if str == [] {
        reveal Pow();
      } else {
        calc <= {
          ToNat_any(str, base, digits);
          ToNat_any(str[..|str| - 1], base, digits) * base + digits[str[|str| - 1]];
          ToNat_any(str[..|str| - 1], base, digits) * base + (base - 1);
          { ToNat_bound(str[..|str| - 1], base, digits);
            LemmaMulInequalityAuto(); }
          (Pow(base, |str| - 1) - 1) * base + base - 1;
          { LemmaMulIsDistributiveAuto(); }
          Pow(base, |str| - 1) * base - 1;
          { reveal Pow(); LemmaMulIsCommutativeAuto(); }
          Pow(base, |str|) - 1;
        }
      }
    }

    function ToInt_any(str: String, minus: Char, base: nat, digits: map<Char, nat>) : (s: int)
      requires base > 0
      requires str != [minus]
      requires NumberStr(str, minus, c => c in digits)
    {
      if [minus] <= str then -(ToNat_any(str[1..], base, digits) as int)
      else
        assert str == [] || str == [str[0]] + str[1..];
        ToNat_any(str, base, digits)
    }
  }

  abstract module ParametricEscaping {
    import opened Wrappers

    type Char(==)
    type String = seq<Char>

    function Escape(str: String, special: set<Char>, escape: Char): String {
      if str == [] then str
      else if str[0] in special then [escape, str[0]] + Escape(str[1..], special, escape)
      else [str[0]] + Escape(str[1..], special, escape)
    }

    datatype UnescapeError =
      EscapeAtEOS

    function Unescape(str: String, escape: Char): Result<String, UnescapeError> {
      if str == [] then Success(str)
      else if str[0] == escape then
        if |str| > 1 then var tl :- Unescape(str[2..], escape); Success([str[1]] + tl)
        else Failure(EscapeAtEOS)
      else var tl :- Unescape(str[1..], escape); Success([str[0]] + tl)
    }

    lemma {:induction false} Unescape_Escape(str: String, special: set<Char>, escape: Char)
      requires escape in special
      ensures Unescape(Escape(str, special, escape), escape) == Success(str)
    {
      if str == [] {
      } else {
        assert str == [str[0]] + str[1..];
        Unescape_Escape(str[1..], special, escape);
      }
    }
  }

  module CharStrConversion refines ParametricConversion {
    type Char = char
  }

  module CharStrEscaping refines ParametricEscaping {
    type Char = char
  }

  const HEX_DIGITS: seq<char> := "0123456789ABCDEF"

  const HEX_TABLE :=
    map[
      '0' := 0, '1' := 1, '2' := 2, '3' := 3, '4' := 4, '5' := 5, '6' := 6, '7' := 7, '8' := 8, '9' := 9,
      'a' := 0xA, 'b' := 0xB, 'c' := 0xC, 'd' := 0xD, 'e' := 0xE, 'f' := 0xF,
      'A' := 0xA, 'B' := 0xB, 'C' := 0xC, 'D' := 0xD, 'E' := 0xE, 'F' := 0xF
    ]

  function OfNat(n: nat, base: int := 10) : (str: string)
    requires 2 <= base <= 16
    ensures |str| == Log(base, n) + 1
    ensures forall c | c in str :: c in HEX_DIGITS[..base]
  {
    CharStrConversion.OfNat_any(n, HEX_DIGITS[..base])
  }

  function OfInt(n: int, base: int := 10) : (str: string)
    requires 2 <= base <= 16
    ensures CharStrConversion.NumberStr(str, '-', c => c in HEX_DIGITS[..base])
  {
    CharStrConversion.OfInt_any(n, HEX_DIGITS[..base], '-')
  }

  function ToNat(str: string, base: int := 10) : (n: nat)
    requires 2 <= base <= 16
    requires forall c | c in str :: c in HEX_TABLE && HEX_TABLE[c] as int < base
    ensures n < Pow(base, |str|)
  {
    CharStrConversion.ToNat_bound(str, base, HEX_TABLE);
    CharStrConversion.ToNat_any(str, base, HEX_TABLE)
  }

  function ToInt(str: string, base: int := 10) : (n: int)
    requires str != "-"
    requires 2 <= base <= 16
    requires CharStrConversion.NumberStr(str, '-', (c: char) => c in HEX_TABLE && HEX_TABLE[c] as int < base)
  {
    CharStrConversion.ToInt_any(str, '-', base, HEX_TABLE)
  }

  function EscapeQuotes(str: string): string {
    CharStrEscaping.Escape(str, {'\"', '\''}, '\\')
  }

  function UnescapeQuotes(str: string): Result<string, CharStrEscaping.UnescapeError> {
    CharStrEscaping.Unescape(str, '\\')
  }

  method Test() { // FIXME {:test}?
    expect OfInt(0, 10) == "0";
    expect OfInt(3, 10) == "3";
    expect OfInt(302, 10) == "302";
    expect OfInt(-3, 10) == "-3";
    expect OfInt(-302, 10) == "-302";
  }

  function OfBool(b: bool) : string {
    if b then "true" else "false"
  }

  function OfChar(c: char) : string {
    [c]
  }

  function Join(sep: string, strs: seq<string>) : string {
    if |strs| == 0 then ""
    else if |strs| == 1 then strs[0]
    else strs[0] + sep + Join(sep, strs[1..])
  }

  function Concat(strs: seq<string>) : string {
    if |strs| == 0 then ""
    else strs[0] + Concat(strs[1..])
  }

  lemma Concat_Join(strs: seq<string>)
    ensures Concat(strs) == Join("", strs)
  {}
}