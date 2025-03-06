module Std.Parsers.StringParsers refines Core {
  export StringParsers reveals *
  export Export extends Core
    provides
      Char,
      Digit,
      DigitNumber,
      Nat,
      Int,
      String,
      ExtractLineCol,
      Wrappers,
      Space,
      WS
    reveals C

  type C = char

  // ##################################
  // String-specific parser combinators
  // ##################################

  opaque function Char(expectedChar: char): (p: Parser<char>)
    // A parser that tests if the current char is the given expected char
  {
    CharTest((c: char) => c == expectedChar, [expectedChar])
  }

  opaque function Space(): (p: Parser<char>)
    // A parser that tests if the current char is a whitespace including newline
  {
    CharTest(c => c in " \t\r\n", "space")
  }

  opaque function WS(): (p: Parser<string>)
  {
    ZeroOrMore(Space())
  }

  opaque function Digit(): (p: Parser<char>)
    // A parser that tests if the current char is a digit and returns it
  {
    CharTest(c => c in "0123456789", "digit")
  }

  opaque function DigitNumber(): (p: Parser<nat>)
    // A parser that returns the current char as a number if it is one
  {
    Map(Digit(), (c: char) =>
          var d := digitToInt(c);
          var n: nat := if d >= 0 then d else 0;
          n
    )
  }

  opaque function Nat(): (p: Parser<nat>)
    // A parser that parses a natural number
  {
    Bind(DigitNumber(),
         (result: nat) =>
           Rep(DigitNumber(),
               (previous: nat, c: nat) =>
                 var r: nat := previous * 10 + c; r,
               result
           )
    )
  }

  opaque function Int(): (p: Parser<int>)
    // A parser that parses a integer, possibly negative
  {
    Bind(Maybe(Char('-')),
         (minusSign: Option<char>) =>
           Map<nat, int>(Nat(), (result: nat) => if minusSign.Some? then 0-result else result))
  }

  opaque function String(expected: string): (p: Parser<string>)
    // A parser that succeeds only if the input starts with the given string
    // Its failure is recoverable, so it's possible to branch to something else
  {
    (input: string) =>
      if |expected| <= |input| && input[0..|expected|] == expected then Success(expected, input[|expected|..])
      else Failure(Recoverable, FailureData("expected '"+expected+"'", input, Option.None))
  }

  // ########################
  // Error handling utilities
  // ########################

  function repeat_(str: string, n: nat): (r: string)
    // Repeats the given string n times
    ensures |r| == |str| * n
  {
    if n == 0 then ""
    else str + repeat_(str, n-1)
  }

  method ExtractLineCol(input: string, pos: nat)
    returns (lineNumber: nat, lineStr: string, colNumber: nat)
    // Returns the line number, the extracted line, and the column number
    // corresponding to a given position in the given input
  {
    lineNumber := 1;
    var startLinePos: nat := 0;
    colNumber := 0;
    var i := 0;
    while i < |input| && i != pos
      invariant 0 <= startLinePos <= i <= |input|
    {
      colNumber := colNumber + 1;
      if input[i] == '\r' && i + 1 < |input| && input[i+1] == '\n' {
        lineNumber := lineNumber + 1;
        colNumber := 0;
        i := i + 1;
        startLinePos := i + 1;
      } else if input[i] in "\r\n" {
        lineNumber := lineNumber + 1;
        colNumber := 0;
        startLinePos := i + 1;
      }
      i := i + 1;
    }
    while i < |input| && input[i] !in "\r\n"
      invariant startLinePos <= i <= |input|
    {
      i := i + 1;
    }
    lineStr := input[startLinePos..i];
  }

  function NatToString(input: nat): string {
    if input < 10 then "0123456789"[input..input + 1] else
    NatToString(input / 10) + NatToString(input % 10)
  }

  function DebugSummary(input: string): string {
    NatToString(|input|) + " \"" +
    (if |input| > 0 then
      match input[0] {
        case '\n' => "\\n"
        case '\r' => "\\r"
        case '\t' => "\\t"
        case c => [c]
      }
    else
      "EOS") + "\"\n"
  }

  function DebugNameSummary(name: string, input: string): string {
    name + ": " + DebugSummary(input)
  }

  function DebugSummaryInput(name: string, input: string): string {
    "> " + DebugNameSummary(name, input)
  }

  function NewIndent(input: string, indent: string): string {
    if |input| == 0 then "" else
    (if input[0] == '\n' then input[..1] + indent else input[..1]) + NewIndent(input[1..], indent)
  }

  method {:print} PrintDebugSummaryOutput<R>(name: string, input: string, result: ParseResult<R>) {
    print "< ", DebugNameSummary(name, input);
    if result.Failure? {
      var failureMessage := FailureToString(input, result);
      print "| R: ", DebugSummary(result.Remaining());
      if |result.Remaining()| < |input| {
        print "| Was committed\n";
      }
      print "| " + NewIndent(failureMessage, "| "), "\n";
    } else {
      print " (Success)\n";
    }
  }

  method FailureToString<R>(input: string, result: ParseResult<R>, printPos: int := -1) returns (failure: string)
    // Util to print the line, the column, and all the error messages
    // associated to a given parse failure
    requires result.Failure?
    decreases result.data
  {
    failure := "";
    failure := failure +
    if printPos == -1 then
      (if result.level == Fatal then "Fatal error" else "Error") + ":\n"
    else "";
    var pos: int := |input| - |result.data.remaining|; // Need the parser to be Valid()
    pos := if pos < 0 then // Could be proved false if parser is Valid()
      0
    else
      pos;
    if printPos != pos {
      var line, lineStr, col := ExtractLineCol(input, pos);
      failure := failure + NatToString(line) + ": " + lineStr + "\n" +
      repeat_(" ", col + 2 + |intToString(line)|) + "^" + "\n";
    }
    failure := failure + result.data.message;
    if result.data.next.Some? {
      failure := failure + ", or\n";
      var subFailure := FailureToString<R>(input, Failure(result.level, result.data.next.value), pos);
      failure := failure + subFailure;
      return failure;
    } else {
      failure := failure + "\n";
      return failure;
    }
  }
}