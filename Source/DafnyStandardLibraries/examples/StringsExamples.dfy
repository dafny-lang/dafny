module StringsExamples {
  import opened Std.Strings
  import opened Std.Wrappers

  method {:test} TestOfInt() {
    expect OfInt(0) == "0";
    expect OfInt(3) == "3";
    expect OfInt(302) == "302";
    expect OfInt(-3) == "-3";
    expect OfInt(-302) == "-302";
  }

  method {:test} TestToInt() {
    expect ToInt("0") == 0;
    expect ToInt("3") == 3;
    expect ToInt("302") == 302;
    expect ToInt("-3") == -3;
    expect ToInt("-302") == -302;
  }

  method {:test} TestOfNat() {
    expect OfNat(0) == "0";
    expect OfNat(1) == "1";
    expect OfNat(3) == "3";
    expect OfNat(302) == "302";
    expect OfNat(3123123213102) == "3123123213102";
  }

  method {:vcs_split_on_every_assert} {:test} TestToNat() {
    expect ToNat("0") == 0;
    expect ToNat("1") == 1;
    expect ToNat("3") == 3;
    expect ToNat("302") == 302;
    expect ToNat("3123123213102") == 3123123213102;
  }

  method {:test} TestEscapeQuotes() {
    expect EscapeQuotes("this message has single \' quotes \' ") == "this message has single \\\' quotes \\\' ";
    expect EscapeQuotes("this message has double \" quotes \" ") == "this message has double \\\" quotes \\\" ";
  }

  method {:test} TestUnescapeQuotes() {
    expect UnescapeQuotes("this message has single \\\' quotes \\\' ") == Some("this message has single \' quotes \' ");
    expect UnescapeQuotes("this message has double \\\" quotes \\\" ") == Some("this message has double \" quotes \" ");
  }

  method {:test} TestOfBool() {
    expect OfBool(true) == "true";
    expect OfBool(false) == "false";
  }

  method {:test} TestOfChar() {
    expect OfChar('c') == "c";
    expect OfChar('f') == "f";
  }
}