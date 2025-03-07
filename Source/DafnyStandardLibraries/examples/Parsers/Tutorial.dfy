module ExampleParsers.Tutorial {
  import opened Std.Parsers.StringParsers

  method {:test} TestSplit1() {
    var nonComma: Parser<string> :=
      OneOrMore(CharTest((c: char) => c != ',', "non-comma"));
    var p :=
      Bind(
        nonComma, (result: string) =>
          Rep(ConcatR(String(","), nonComma),
              (acc, elem) => acc + [elem],
              [result]
          ));

    expect p("abc,d,efg") == ParseResult.Success(["abc","d","efg"], "");
    var source := "abc,d,,";
    expect p(source)
        == ParseResult.Failure(Recoverable, FailureData("expected a non-comma", ",", Option.None));
    var failureMessage := FailureToString(source, p(source));
    expect failureMessage
        == "Error:"               + "\n" +
           "1: abc,d,,"           + "\n" +
           "         ^"           + "\n" +
           "expected a non-comma" + "\n";
  }

  function flatten<A>(): ((A, (A, A))) -> (A, A, A) {
    (input: (A, (A, A))) =>
      (input.0, input.1.0, input.1.1)
  }

  method {:test} TestTicTacToe() {
    var x := OrSeq(
      [
        String("O"), String("X"), String(" ")
      ]);
    var v := String("|");
    var row := Map(Concat(x, ConcatR(v, Concat(x, ConcatR(v, x)))),
                   flatten<string>());
    var sep := String("\n-+-+-\n");
    var grid := Map(
      Concat(row, ConcatR(sep, Concat(row, ConcatR(sep, row)))),
      flatten<(string, string, string)>())
      ;
    var input := "O|X| \n-+-+-\nX|O| \n-+-+-\nP| |O";
    // 012345 678901 234567 890123 45678
    var r := grid(input);
    expect r.IsFailure();
    expect |input| - |r.data.remaining| == 24;
    expect r.data.message == "expected 'O'";
    expect r.data.next.Some?;
    expect r.data.next.value.message == "expected 'X'";
    expect r.data.next.value.next.Some?;
    expect r.data.next.value.next.value.message == "expected ' '";
    expect r.data.next.value.next.value.next.None?;
    var failureMessage := FailureToString(input, r);
    expect failureMessage
        == "Error:"           + "\n" +
           "5: P| |O"         + "\n" +
           "   ^"             + "\n" +
           "expected 'O', or" + "\n" +
           "expected 'X', or" + "\n" +
           "expected ' '"     + "\n";
  }
}

module ExampleParsers.TestTutorialParsersBuilders {
  import opened Std.Parsers.StringBuilders

  method {:test} TestSplit1() {
    var nonComma: B<string> :=
      CharTest((c: char) => c != ',', "non-comma").OneOrMore();
    var p :=
      nonComma.Bind(
        (result: string) =>
          S(",").e_I(nonComma).Rep([result],
                                   (acc: seq<string>, elem: string) => acc + [elem]
          ));

    expect p.apply("abc,d,efg") == P.ParseResult.Success(["abc","d","efg"], "");
  }

  method {:test} TestTicTacToe() {
    var x := O([ S("O"), S("X"), S(" ") ]);
    var v := S("|");
    var row := x.I_e(v).I_I(x).I_e(v).I_I(x);   // I stands for included, e for excluded
    var sep := S("\n-+-+-\n");
    var grid := row.I_e(sep).I_I(row).I_e(sep).I_I(row);
    var input := "O|X| \n-+-+-\nX|O| \n-+-+-\nP| |O";
    var r := grid.apply(input);
    var failureMessage := P.FailureToString(input, r);
    expect failureMessage
        == "Error:"           + "\n" +
           "5: P| |O"         + "\n" +
           "   ^"             + "\n" +
           "expected 'O', or" + "\n" +
           "expected 'X', or" + "\n" +
           "expected ' '"     + "\n";
  }
}