/**
The Strings module enables converting between numbers such as nat and int, and String
 */
@DisableNonlinearArithmetic
module Std.Strings {
  import opened Wrappers
  import opened Arithmetic.Power
  import opened Arithmetic.Logarithm
  import Arithmetic

  /**
  Refine this module to use it.
  The refinee must define:
    - the type of character used, Char
    - a conversion from nat to Char (the chars sequences) and vice versa (charToDigit)
   */
  @DisableNonlinearArithmetic
  abstract module ParametricConversion refines Arithmetic.LittleEndianNat {
    import opened Wrappers

    type Char(==)
    type String = seq<Char>

    type CharSeq = chars: seq<Char> | |chars| > 1 witness *
    // Canoncial digit characters: converting to strings will uses these characters.
    const chars: CharSeq
    const base := |chars|
    // All recognized digit characters: converting from strings will use this map,
    // which may associate multiple characters with the same digit.
    const charToDigit: map<Char, digit>

    lemma CharsConsistent()
      ensures forall c <- chars :: c in charToDigit && chars[charToDigit[c]] == c

    function BASE(): nat {
      base
    }

    predicate IsDigitChar(c: Char) {
      c in charToDigit
    }

    function OfDigits(digits: seq<digit>) : (str: String)
      ensures forall c <- str :: c in chars
      ensures |str| == |digits|
    {
      if digits == [] then []
      else
        assert digits[0] in digits;
        assert forall d | d in digits[1..] :: d in digits;
        OfDigits(digits[1..]) + [chars[digits[0]]]
    }

    /*
    Convert a natural number into its String representation
    */
    function OfNat(n: nat) : (str: String)
      ensures |str| == Log(base, n) + 1
      ensures forall c <- str :: c in chars
    {
      if n == 0 then  [chars[0]]
      else LemmaFromNatLen2(n); OfDigits(FromNat(n))
    }

    predicate IsNumberStr(str: String, minus: Char) {
      str != [] ==>
        && (str[0] == minus || str[0] in charToDigit)
        && forall c <- str[1..] :: IsDigitChar(c)
    }

    /*
    Convert an integer into its String representation, 
    given a particular minus character.
    */
    function OfInt(n: int, minus: Char) : (str: String)
      ensures IsNumberStr(str, minus)
    {
      CharsConsistent();
      if n >= 0 then OfNat(n)
      else [minus] + OfNat(-n)
    }

    /**
    Convert a String that represents a natural number, back into that number.
     */
    @IsolateAssertions
    function ToNat(str: String) : (n: nat)
      requires forall c <- str :: IsDigitChar(c)
    {
      if str == [] then 0
      else
        LemmaMulNonnegativeAuto();
        var c := str[|str| - 1];
        assert IsDigitChar(c);
        ToNat(str[..|str| - 1]) * base + charToDigit[c]
    }

    lemma {:induction false} ToNatBound(str: String)
      requires base > 0
      requires forall c <- str :: IsDigitChar(c)
      ensures ToNat(str) < Pow(base, |str|)
    {
      if str == [] {
      } else {
        calc <= {
          ToNat(str);
          { assert IsDigitChar(str[|str| - 1]); }
          ToNat(str[..|str| - 1]) * base + charToDigit[str[|str| - 1]];
          ToNat(str[..|str| - 1]) * base + (base - 1);
          { ToNatBound(str[..|str| - 1]);
            LemmaMulInequalityAuto(); }
          (Pow(base, |str| - 1) - 1) * base + base - 1;
          { LemmaMulIsDistributiveAuto(); }
          Pow(base, |str| - 1) * base - 1;
          {  LemmaMulIsCommutativeAuto(); }
          Pow(base, |str|) - 1;
        }
      }
    }

    /**
    Convert a String that represents a number, back into that number
     */
    function ToInt(str: String, minus: Char): (s: int)
      requires str != [minus]
      requires IsNumberStr(str, minus)
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

    /**
    Use an escape character to convert a String to its escaped form.
     */
    function Escape(str: String, mustEscape: set<Char>, escape: Char): String {
      if str == [] then str
      else if str[0] in mustEscape then [escape, str[0]] + Escape(str[1..], mustEscape, escape)
      else [str[0]] + Escape(str[1..], mustEscape, escape)
    }

    /**
    Unescape a String using the given escape character.
     */
    function Unescape(str: String, escape: Char): Option<String> {
      if str == [] then Some(str)
      else if str[0] == escape then
        if |str| > 1 then var tl :- Unescape(str[2..], escape); Some([str[1]] + tl)
        else None
      else var tl :- Unescape(str[1..], escape); Some([str[0]] + tl)
    }

    lemma {:induction false} Unescape_Escape(str: String, special: set<Char>, escape: Char)
      requires escape in special
      ensures Unescape(Escape(str, special, escape), escape) == Some(str)
    {
      if str == [] {
      } else {
        assert str == [str[0]] + str[1..];
        Unescape_Escape(str[1..], special, escape);
      }
    }
  }

  @DisableNonlinearArithmetic
  module HexConversion refines ParametricConversion {
    type Char = char
    const HEX_DIGITS: seq<char> := "0123456789ABCDEF"
    const chars := HEX_DIGITS
    const charToDigit :=
      map[
        '0' := 0, '1' := 1, '2' := 2, '3' := 3, '4' := 4, '5' := 5, '6' := 6, '7' := 7, '8' := 8, '9' := 9,
        'a' := 0xA, 'b' := 0xB, 'c' := 0xC, 'd' := 0xD, 'e' := 0xE, 'f' := 0xF,
        'A' := 0xA, 'B' := 0xB, 'C' := 0xC, 'D' := 0xD, 'E' := 0xE, 'F' := 0xF
      ]
    // The size of the map makes this impractical to verify easily.
    @Axiom
    lemma CharsConsistent()
      ensures forall c <- chars :: c in charToDigit && chars[charToDigit[c]] == c
  }

  @DisableNonlinearArithmetic
  module DecimalConversion refines ParametricConversion {
    type Char = char
    const DIGITS: seq<char> := "0123456789"
    const chars := DIGITS
    const charToDigit :=
      map[
        '0' := 0, '1' := 1, '2' := 2, '3' := 3, '4' := 4, '5' := 5, '6' := 6, '7' := 7, '8' := 8, '9' := 9
      ]
    lemma CharsConsistent()
      ensures forall c <- chars :: c in charToDigit && chars[charToDigit[c]] == c
    {}
  }

  module CharStrEscaping refines ParametricEscaping {
    type Char = char
  }

  /*
  Convert a natural number into its String representation for a decimal number system
  */
  function OfNat(n: nat) : (str: string)
    ensures |str| == Log(DecimalConversion.base, n) + 1
    ensures forall c | c in str :: c in DecimalConversion.chars
  {
    DecimalConversion.OfNat(n)
  }

  /*
  Convert an integer into its String representation for a decimal number system
  */
  function OfInt(n: int) : (str: string)
    ensures DecimalConversion.IsNumberStr(str, '-')
  {
    DecimalConversion.OfInt(n, '-')
  }

  /**
  Given a natural number represented as a decimal number in a String, back into an integer
   */
  function ToNat(str: string) : (n: nat)
    requires forall c <- str :: DecimalConversion.IsDigitChar(c)
    ensures n < Pow(DecimalConversion.base, |str|)
  {
    DecimalConversion.ToNatBound(str);
    DecimalConversion.ToNat(str)
  }

  /**
  Given an integer number represented as a decimal number in a String, back into an integer
   */
  function ToInt(str: string) : (n: int)
    requires str != "-"
    requires DecimalConversion.IsNumberStr(str, '-')
  {
    DecimalConversion.ToInt(str, '-')
  }

  /**
  Use an escape character to convert a String to its escaped form.
    */
  function EscapeQuotes(str: string): string {
    CharStrEscaping.Escape(str, {'\"', '\''}, '\\')
  }

  /**
  Unescape a String using the given escape character.
    */
  function UnescapeQuotes(str: string): Option<string> {
    CharStrEscaping.Unescape(str, '\\')
  }

  /**
  Convert a boolean into its string representation
   */
  function OfBool(b: bool) : string {
    if b then "true" else "false"
  }

  /**
  Convert a char into its string representation
   */
  function OfChar(c: char) : string {
    [c]
  }
}
