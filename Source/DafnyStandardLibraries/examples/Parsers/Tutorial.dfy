/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

module ExampleParsers.Tutorial {
  import opened Std.Parsers.StringParsers

  method {:test} TestSplit1() {
    var nonComma: Parser<string> :=
      OneOrMore(CharTest((c: char) => c != ',', "non-comma"));
    var p :=
      Bind(
        nonComma, (result: string) =>
          Rep(ConcatKeepRight(String(","), nonComma),
              (acc, elem) => acc + [elem],
              [result]
          ));
    var input := "abc,d,efg";
    var result := p(ToInput(input));
    expect result.ParseSuccess?;
    expect result.result == ["abc","d","efg"];
    var source := "abc,d,,";
    expect p(ToInput(source))
        == ParseResult.ParseFailure(Recoverable, FailureData("expected a non-comma", A.Seq.Slice(source, |source| - 1, |source|), Option.None));
    var failureMessage := FailureToString(source, p(ToInput(source)));
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
    var row := Map(Concat(x, ConcatKeepRight(v, Concat(x, ConcatKeepRight(v, x)))),
                   flatten<string>());
    var sep := String("\n-+-+-\n");
    var grid := Map(
      Concat(row, ConcatKeepRight(sep, Concat(row, ConcatKeepRight(sep, row)))),
      flatten<(string, string, string)>())
      ;
    var input := ToInput("O|X| \n-+-+-\nX|O| \n-+-+-\nP| |O");
    // 012345 678901 234567 890123 45678
    var r := grid(input);
    expect r.IsFailure();
    expect A.Length(input) - A.Length(r.data.remaining) == 24;
    var failureMessage := FailureToString(input.data, r);
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
      CharTest((c: char) => c != ',', "non-comma").Rep1();
    var p :=
      nonComma.Then(
        (result: string) =>
          S(",").e_I(nonComma).RepFold(
            [result],
            (acc: seq<string>, elem: string) => acc + [elem]
          ));
    var source := "abc,d,efg";
    expect p.Apply(source) == ParseResult.ParseSuccess(["abc","d","efg"], ToInputEnd(source));
  }

  method {:test} TestTicTacToe() {
    var x := O([ S("O"), S("X"), S(" ") ]);
    var v := S("|");
    var row := x.I_e(v).I_I(x).I_e(v).I_I(x);   // I stands for included, e for excluded
    var sep := S("\n-+-+-\n");
    var grid := row.I_e(sep).I_I(row).I_e(sep).I_I(row);
    var input := "O|X| \n-+-+-\nX|O| \n-+-+-\nP| |O";
    var r := grid.Apply(input);
    expect r.ParseFailure?;
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