module StringsExamples {
  import opened DafnyStdLibs.Strings

  method {:test} Test() {
    expect OfInt(0) == "0";
    expect OfInt(3) == "3";
    print "OfInt(302), " + OfInt(302);
    expect OfInt(302) == "302";
    expect OfInt(-3) == "-3";
    expect OfInt(-302) == "-302";
  }
}