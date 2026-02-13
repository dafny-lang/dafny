module StringsExamples {
  import opened Std.Strings
  import opened Std.Wrappers

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