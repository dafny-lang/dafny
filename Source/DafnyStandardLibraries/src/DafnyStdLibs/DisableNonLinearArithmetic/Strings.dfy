module DafnyStdLibs.Strings {
  import opened Wrappers
  import opened Arithmetic.Power
  import opened Arithmetic.Logarithm

  abstract module ParametricConversion {
    import opened Wrappers
    import opened Arithmetic.Mul
    import opened Arithmetic.DivMod
    import opened Arithmetic.Power
    import opened Arithmetic.Logarithm

    type Char(==)
    type String = seq<Char>
    type CharSet = chars: seq<Char> | |chars| > 1 witness *
    const chars: CharSet
    const base := |chars|
    const charMap: map<Char, nat> // TODO build from chars? 

    // TODO use LittleEndiaNat for digits
    function Digits(n: nat): (digits: seq<int>)
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
        var digits' := Digits(n / base);
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

    function OfDigits(digits: seq<int>) : (str: String)
      requires forall d | d in digits :: 0 <= d < base
      ensures forall c | c in str :: c in chars
      ensures |str| == |digits|
    {
      if digits == [] then []
      else
        assert digits[0] in digits;
        assert forall d | d in digits[1..] :: d in digits;
        [chars[digits[0]]] + OfDigits(digits[1..])
    }

    function OfNat(n: nat) : (str: String)
      ensures |str| == Log(base, n) + 1
      ensures forall c | c in str :: c in chars
    {
      if n == 0 then reveal Log(); [chars[0]]
      else OfDigits(Digits(n))
    }

    predicate NumberStr(str: String, minus: Char, isDigit: Char -> bool) {
      str != [] ==>
        && (str[0] == minus || isDigit(str[0]))
        && forall c | c in str[1..] :: isDigit(c)
    }

    function OfInt(n: int, minus: Char) : (str: String)
      ensures NumberStr(str, minus, c => c in chars)
    {
      if n >= 0 then OfNat(n)
      else [minus] + OfNat(-n)
    }

    function {:vcs_split_on_every_assert} ToNat(str: String) : (n: nat)
      requires forall c | c in str :: c in charMap
    {
      if str == [] then 0
      else
        LemmaMulNonnegativeAuto();
        ToNat(str[..|str| - 1]) * base + charMap[str[|str| - 1]]
    }

    lemma {:induction false} ToNat_bound(str: String)
      requires base > 0
      requires forall c | c in str :: c in charMap
      requires forall c | c in str :: charMap[c] < base
      ensures ToNat(str) < Pow(base, |str|)
    {
      if str == [] {
        reveal Pow();
      } else {
        calc <= {
          ToNat(str);
          ToNat(str[..|str| - 1]) * base + charMap[str[|str| - 1]];
          ToNat(str[..|str| - 1]) * base + (base - 1);
          { ToNat_bound(str[..|str| - 1]);
            LemmaMulInequalityAuto(); }
          (Pow(base, |str| - 1) - 1) * base + base - 1;
          { LemmaMulIsDistributiveAuto(); }
          Pow(base, |str| - 1) * base - 1;
          { reveal Pow(); LemmaMulIsCommutativeAuto(); }
          Pow(base, |str|) - 1;
        }
      }
    }

    function ToInt(str: String, minus: Char) : (s: int)
      requires str != [minus]
      requires NumberStr(str, minus, c => c in charMap)
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
    ensures DecimalConversion.NumberStr(str, '-', c => c in DecimalConversion.chars)
  {
    DecimalConversion.OfInt(n, '-')
  }

  function ToNat(str: string) : (n: nat)
    requires forall c | c in str :: c in DecimalConversion.charMap && DecimalConversion.charMap[c] as int < DecimalConversion.base
    ensures n < Pow(DecimalConversion.base, |str|)
  {
    DecimalConversion.ToNat_bound(str);
    DecimalConversion.ToNat(str)
  }

  function ToInt(str: string) : (n: int)
    requires str != "-"
    requires DecimalConversion.NumberStr(str, '-', (c: char) => c in DecimalConversion.charMap && DecimalConversion.charMap[c] as int < DecimalConversion.base)
  {
    DecimalConversion.ToInt(str, '-')
  }

  function EscapeQuotes(str: string): string {
    CharStrEscaping.Escape(str, {'\"', '\''}, '\\')
  }

  function UnescapeQuotes(str: string): Result<string, CharStrEscaping.UnescapeError> {
    CharStrEscaping.Unescape(str, '\\')
  }

  method Test() { // FIXME {:test}?
    expect OfInt(0) == "0";
    expect OfInt(3) == "3";
    expect OfInt(302) == "302";
    expect OfInt(-3) == "-3";
    expect OfInt(-302) == "-302";
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
