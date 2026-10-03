module StringsExamples {
  import opened Std.Strings
  import opened Std.Wrappers
  import H = Std.Strings.HexConversion
  import D = Std.Strings.DecimalConversion

  @IsolateAssertions
  lemma DecimalRoundTrips(n: nat, i: int) {
    LemmaNatRoundTrip(n);
    assert ToNat(OfNat(n)) == n;
    LemmaIntRoundTrip(i);
    assert ToInt(OfInt(i)) == i;
    D.LemmaNatRoundTrip(n);
    assert D.ToNat(D.OfNat(n)) == n;
    D.LemmaIntRoundTrip(i);
    assert D.ToInt(D.OfInt(i, '-'), '-') == i;
  }

  @IsolateAssertions
  lemma HexRoundTrips(n: nat, i: int)
    ensures forall c <- H.OfNat(n) :: H.IsDigitChar(c)
    ensures H.ToNat(H.OfNat(n)) == n
    ensures H.OfInt(i, '-') != ['-']
    ensures H.ToInt(H.OfInt(i, '-'), '-') == i
  {
    H.LemmaIntRoundTrip(i, '-');
    assert H.ToInt(H.OfInt(i, '-'), '-') == i;
    H.LemmaNatRoundTrip(n);
    assert H.ToNat(H.OfNat(n)) == n;
  }

  @IsolateAssertions
  @Test
  method TestRoundTrips() {
    for i := -512 to 513 {
      LemmaIntRoundTrip(i);
      expect ToInt(OfInt(i)) == i;
      HexRoundTrips(if i >= 0 then i else 0, i);
      expect H.ToInt(H.OfInt(i, '-'), '-') == i;
      if i >= 0 {
        LemmaNatRoundTrip(i);
        expect ToNat(OfNat(i)) == i;
        expect H.ToNat(H.OfNat(i)) == i;
      }
    }
  }

  @IsolateAssertions
  @Test
  method TestLargeRoundTrips() {
    // Exercise arbitrary-precision values beyond machine integer widths.
    var large := 1234567890123456789012345678901234567890;
    H.LemmaIntRoundTrip(-large, '~');
    expect H.ToInt(H.OfInt(-large, '~'), '~') == -large;
    LemmaNatRoundTrip(large);
    expect ToNat(OfNat(large)) == large;
    LemmaIntRoundTrip(-large);
    expect ToInt(OfInt(-large)) == -large;
  }

  @IsolateAssertions
  @Test
  method TestHexNormalization() {
    expect H.OfNat(0xABCDEF) == "ABCDEF";
    expect H.ToNat("abcdef") == 0xABCDEF;
    expect H.ToNat("aBcDeF") == 0xABCDEF;
    expect H.OfNat(H.ToNat("00ab")) == "AB";
  }

  @IsolateAssertions
  @Test
  method TestDecimalNormalization() {
    expect OfInt(ToInt("-0")) == "0";
    expect OfNat(ToNat("0007")) == "7";
  }

  @IsolateAssertions
  @Test
  method TestEmptyParses() {
    expect ToNat("") == 0;
    expect H.ToNat("") == 0;
    expect ToInt("") == 0;
    expect H.ToInt("", '-') == 0;
  }

  @IsolateAssertions
  @Test
  method TestSignCollision() {
    // A digit used as the sign can change a positive number's interpretation.
    expect H.OfInt(0xAB, 'A') == "AB";
    expect H.ToInt("AB", 'A') == -0xB;
  }

  @Test
  method TestOfInt() {
    expect OfInt(0) == "0";
    expect OfInt(3) == "3";
    expect OfInt(302) == "302";
    expect OfInt(-3) == "-3";
    expect OfInt(-302) == "-302";
  }

  @Test
  method TestToInt() {
    expect ToInt("0") == 0;
    expect ToInt("3") == 3;
    expect ToInt("302") == 302;
    expect ToInt("-3") == -3;
    expect ToInt("-302") == -302;
  }

  @Test
  method TestOfNat() {
    expect OfNat(0) == "0";
    expect OfNat(1) == "1";
    expect OfNat(3) == "3";
    expect OfNat(302) == "302";
    expect OfNat(3123123213102) == "3123123213102";
  }

  @IsolateAssertions
  @Test
  method TestToNat() {
    expect ToNat("0") == 0;
    expect ToNat("1") == 1;
    expect ToNat("3") == 3;
    expect ToNat("302") == 302;
    expect ToNat("3123123213102") == 3123123213102;
  }

  @Test
  method TestEscapeQuotes() {
    expect EscapeQuotes("this message has single \' quotes \' ") == "this message has single \\\' quotes \\\' ";
    expect EscapeQuotes("this message has double \" quotes \" ") == "this message has double \\\" quotes \\\" ";
  }

  @Test
  method TestUnescapeQuotes() {
    expect UnescapeQuotes("this message has single \\\' quotes \\\' ") == Some("this message has single \' quotes \' ");
    expect UnescapeQuotes("this message has double \\\" quotes \\\" ") == Some("this message has double \" quotes \" ");
  }

  @Test
  method TestOfBool() {
    expect OfBool(true) == "true";
    expect OfBool(false) == "false";
  }

  @Test
  method TestOfChar() {
    expect OfChar('c') == "c";
    expect OfChar('f') == "f";
  }
}

// Existing refinements need no additional abstract lemma. A refinement can
// establish the indexed digit law when it wants to use the new round trips.
module BinaryConversionExample refines Std.Strings.ParametricConversion {
  type Char = char
  const chars := "01"
  const charToDigit := map['0' := 0, '1' := 1]

  lemma CharsConsistent()
    ensures forall c <- chars :: c in charToDigit && chars[charToDigit[c]] == c
  {}

  @IsolateAssertions
  lemma RoundTrips(n: nat, i: int, digits: seq<digit>) {
    assert DigitCharsConsistent();
    LemmaOfIntToInt(i, '~');
    assert ToInt(OfInt(i, '~'), '~') == i;
    LemmaOfNatToNat(n);
    assert ToNat(OfNat(n)) == n;
    LemmaOfDigitsToNat(digits);
    assert ToNat(OfDigits(digits)) == ToNatRight(digits);
  }

  @IsolateAssertions
  @Test
  method TestBinaryDigits() {
    var empty: seq<digit> := [];
    var digits: seq<digit> := [1, 0, 1, 1];
    var padded: seq<digit> := [1, 0, 0];
    expect OfDigits(empty) == "";
    expect ToNat(OfDigits(empty)) == 0;
    expect OfDigits(digits) == "1101";
    expect ToNat(OfDigits(digits)) == 13;
    expect OfDigits(padded) == "001";
    expect ToNat(OfDigits(padded)) == 1;
  }
}

// CharsConsistent alone intentionally still permits repeated characters.
// This refinement documents why the new generic lemmas need their premise.
module RepeatedDigitExample refines Std.Strings.ParametricConversion {
  type Char = char
  const chars := "00"
  const charToDigit := map['0' := 0]

  lemma CharsConsistent()
    ensures forall c <- chars :: c in charToDigit && chars[charToDigit[c]] == c
  {}

  @IsolateAssertions
  @Test
  method TestRepeatedDigit() {
    ghost var decodedSecondDigit := charToDigit[chars[1]];
    assert decodedSecondDigit == 0;
    assert DigitCharsConsistent() ==> decodedSecondDigit == 1;
    assert !DigitCharsConsistent();
    expect OfNat(1) == "0";
    expect ToNat(OfNat(1)) == 0;
  }
}
