/**
The Strings module enables converting between numbers such as nat and int, and String
 */
module DafnyStdLibs.Strings {
  import opened Wrappers
  import opened Arithmetic.Power
  import opened Arithmetic.Logarithm
  import Arithmetic

  abstract module ParametricConversion refines Arithmetic.LittleEndianNat {
    import opened Wrappers

    type Char(==)
    type String = seq<Char>
    type CharSet = chars: seq<Char> | |chars| > 1 witness *
    const chars: CharSet
    const base := |chars|
    const charMap: map<Char, uint>

    function BASE(): nat {
      base
    }

    function OfDigits(digits: seq<uint>) : (str: String)
      requires forall d | d in digits :: 0 <= d < base
      ensures forall c <- str :: c in chars
      ensures |str| == |digits|
    {
      if digits == [] then []
      else
        assert digits[0] in digits;
        assert forall d | d in digits[1..] :: d in digits;
        OfDigits(digits[1..]) + [chars[digits[0]]]
    }

    function OfNat(n: nat) : (str: String)
      ensures |str| == Log(base, n) + 1
      ensures forall c <- str :: c in chars
    {
      if n == 0 then reveal Log(); [chars[0]]
      else LemmaFromNatLen2(n); OfDigits(FromNat(n))
    }

    predicate OfNumberStr(str: String, minus: Char) {
      str != [] ==>
        && (str[0] == minus || str[0] in chars)
        && forall c <- str[1..] :: c in chars
    }

    predicate ToNumberStr(str: String, minus: Char) {
      str != [] ==>
        && (str[0] == minus || str[0] in charMap)
        && forall c <- str[1..] :: c in charMap
    }

    function OfInt(n: int, minus: Char) : (str: String)
      ensures OfNumberStr(str, minus)
    {
      if n >= 0 then OfNat(n)
      else [minus] + OfNat(-n)
    }

    function {:vcs_split_on_every_assert} ToNat(str: String) : (n: nat)
      requires forall c <- str :: c in charMap
    {
      if str == [] then 0
      else
        LemmaMulNonnegativeAuto();
        ToNat(str[..|str| - 1]) * base + charMap[str[|str| - 1]]
    }

    lemma {:induction false} ToNatBound(str: String)
      requires base > 0
      requires forall c <- str :: c in charMap
      requires forall c <- str :: charMap[c] < base
      ensures ToNat(str) < Pow(base, |str|)
    {
      if str == [] {
        reveal Pow();
      } else {
        calc <= {
          ToNat(str);
          ToNat(str[..|str| - 1]) * base + charMap[str[|str| - 1]];
          ToNat(str[..|str| - 1]) * base + (base - 1);
          { ToNatBound(str[..|str| - 1]);
            LemmaMulInequalityAuto(); }
          (Pow(base, |str| - 1) - 1) * base + base - 1;
          { LemmaMulIsDistributiveAuto(); }
          Pow(base, |str| - 1) * base - 1;
          { reveal Pow(); LemmaMulIsCommutativeAuto(); }
          Pow(base, |str|) - 1;
        }
      }
    }

    function ToInt(str: String, minus: Char): (s: int)
      requires str != [minus]
      requires ToNumberStr(str, minus)
    {
      if [minus] <= str then -(ToNat(str[1..]) as int)
      else
        assert str == [] || str == [str[0]] + str[1..];
        ToNat(str)
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

  module HexConversion refines ParametricConversion {
    type Char = char
    const HEX_DIGITS: seq<char> := "0123456789ABCDEF"
    const chars := HEX_DIGITS
    const charMap :=
      map[
        '0' := 0, '1' := 1, '2' := 2, '3' := 3, '4' := 4, '5' := 5, '6' := 6, '7' := 7, '8' := 8, '9' := 9,
        'a' := 0xA, 'b' := 0xB, 'c' := 0xC, 'd' := 0xD, 'e' := 0xE, 'f' := 0xF,
        'A' := 0xA, 'B' := 0xB, 'C' := 0xC, 'D' := 0xD, 'E' := 0xE, 'F' := 0xF
      ]
  }

  module DecimalConversion refines ParametricConversion {
    type Char = char
    const DIGITS: seq<char> := "0123456789"
    const chars := DIGITS
    const charMap :=
      map[
        '0' := 0, '1' := 1, '2' := 2, '3' := 3, '4' := 4, '5' := 5, '6' := 6, '7' := 7, '8' := 8, '9' := 9
      ]
  }

  module CharStrEscaping refines ParametricEscaping {
    type Char = char
  }

  function OfNat(n: nat) : (str: string)
    ensures |str| == Log(DecimalConversion.base, n) + 1
    ensures forall c | c in str :: c in DecimalConversion.chars
  {
    DecimalConversion.OfNat(n)
  }

  function OfInt(n: int) : (str: string)
    ensures DecimalConversion.OfNumberStr(str, '-')
  {
    DecimalConversion.OfInt(n, '-')
  }

  function ToNat(str: string) : (n: nat)
    requires forall c <- str :: c in DecimalConversion.charMap && DecimalConversion.charMap[c] as int < DecimalConversion.base
    ensures n < Pow(DecimalConversion.base, |str|)
  {
    DecimalConversion.ToNatBound(str);
    DecimalConversion.ToNat(str)
  }

  function ToInt(str: string) : (n: int)
    requires str != "-"
    requires DecimalConversion.ToNumberStr(str, '-')
  {
    DecimalConversion.ToInt(str, '-')
  }

  function EscapeQuotes(str: string): string {
    CharStrEscaping.Escape(str, {'\"', '\''}, '\\')
  }

  function UnescapeQuotes(str: string): Result<string, CharStrEscaping.UnescapeError> {
    CharStrEscaping.Unescape(str, '\\')
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
