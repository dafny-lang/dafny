module Std.Parsers.InputString refines AbstractInput {
  datatype Input_ = Input(data: seq<char>, start: int, end: int) {
    ghost predicate Valid() {
      0 <= start <= end <= |data|
    }
    function ToString(): string {
      data[start..end]
    }
  }

  type Input = x: Input_ | x.Valid()
  type C = char

  function View(self: Input): (r: seq<C>)
    ensures |View(self)| == Length(self) {
    self.data[self.start..self.end]
  }
  function Length(self: Input): nat { self.end - self.start  }
  function CharAt(self: Input, i: int): C
    ensures CharAt(self, i) == View(self)[i]  { self.data[self.start + i] }
  function Drop(self: Input, start: int): Input
    ensures View(self)[start..] == View(Drop(self, start)) { Input(self.data, self.start + start, self.end) }
  function Slice(self: Input, start: int, end: int): Input
    ensures View(self)[start..end] == View(Slice(self, start, end)) { Input(self.data, self.start + start, self.start + end) }
  predicate Equals(self: Input, other: Input)
    ensures Equals(self, other) <==> View(self) == View(other)
  {
    self == other
  }
}

module Std.Parsers.StringParsers refines Core {
  export StringParsers reveals *
  export Export extends Core
    provides
      CodeLocation,
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

  import A = InputString

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
          var d := DigitToInt(c);
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
    (input: Input) =>
      if |expected| <= A.Length(input) && A.Slice(input, 0, |expected|).ToString() == expected then
        Success(expected, A.Drop(input, |expected|))
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

  datatype CodeLocation = CodeLocation(lineNumber: nat, colNumber: nat, lineStr: string)
  datatype ExtractLineMutableState = ExtractLineMutableState(input: string, pos: nat, startLinePos: nat, i: nat, lineNumber: nat, colNumber: nat)

  ghost function ExtractLineColSpecAux(vars: ExtractLineMutableState): (res: ExtractLineMutableState)
    requires 0 <= vars.startLinePos <= vars.i <= |vars.input|
    decreases |vars.input| - vars.i
    ensures 0 <= res.startLinePos <= res.i <= |res.input|
    ensures !(res.i < |res.input| && res.i != res.pos) // Negation of the while guard
  {
    if vars.i < |vars.input| && vars.i != vars.pos then
      var colNumber := vars.colNumber + 1;
      if vars.input[vars.i] == '\r' && vars.i + 1 < |vars.input| && vars.input[vars.i+1] == '\n' then
        //var startLinePos := i + 1; // ORIGINAL BUG: vars.i + 1
        ExtractLineColSpecAux(ExtractLineMutableState(vars.input, vars.pos, vars.i + 2, vars.i + 2, vars.lineNumber + 1, 0))
      else if vars.input[vars.i] in "\r\n" then
        var lineNumber := vars.lineNumber + 1;
        var colNumber := 0;
        var startLinePos := vars.i + 1;
        ExtractLineColSpecAux(ExtractLineMutableState(vars.input, vars.pos, startLinePos, vars.i + 1, lineNumber, colNumber))
      else
        ExtractLineColSpecAux(ExtractLineMutableState(vars.input, vars.pos, vars.startLinePos, vars.i + 1, vars.lineNumber, colNumber))
    else
      vars
  }
  opaque ghost function ExtractLineColSpecAux2(vars: ExtractLineMutableState): (res: ExtractLineMutableState)
    requires 0 <= vars.startLinePos <= vars.i <= |vars.input|
    ensures 0 <= res.startLinePos <= res.i <= |res.input|
    decreases |vars.input| - vars.i
    ensures !(res.i < |res.input| && res.input[res.i] !in "\r\n") // Negation of the while guard  
  {
     if vars.i < |vars.input| && vars.input[vars.i] !in "\r\n" then // Second loop
      ExtractLineColSpecAux2(vars.(i := vars.i + 1))
    else
      vars
  }
  opaque ghost function ToCodeLocation(vars: ExtractLineMutableState): CodeLocation
    requires 0 <= vars.startLinePos <= vars.i <= |vars.input|
  {
    CodeLocation(vars.lineNumber, vars.colNumber, vars.input[vars.startLinePos..vars.i])
  }
  // Returns the line number, the extracted line, and the column number
  // corresponding to a given position in the given input
  // If you ask, the method was created first and then lifted up to a function
  opaque function ExtractLineCol(input: string, pos: nat):  (output: CodeLocation)
  {
    var vars := ExtractLineColSpecAux(ExtractLineMutableState(input, pos, 0, 0, 1, 0));
    var vars := ExtractLineColSpecAux2(vars);
    ToCodeLocation(vars)
  } by method {
    var lineNumber, colNumber, lineStr;
    lineNumber := 1;
    var startLinePos: nat := 0;
    colNumber := 0;
    var i := 0;
    reveal ExtractLineCol();
    assert ExtractLineCol(input, pos) == ToCodeLocation(ExtractLineColSpecAux2(ExtractLineColSpecAux(ExtractLineMutableState(input, pos, startLinePos, i, lineNumber, colNumber))));
    while i < |input| && i != pos
      invariant 0 <= startLinePos <= i <= |input|
      invariant 
        ToCodeLocation(ExtractLineColSpecAux2(ExtractLineColSpecAux(
          ExtractLineMutableState(input, pos, startLinePos, i, lineNumber, colNumber))))
        == ExtractLineCol(input, pos)
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
    assert ExtractLineCol(input, pos) == ToCodeLocation(ExtractLineColSpecAux2(ExtractLineMutableState(input, pos, startLinePos, i, lineNumber, colNumber)));
    reveal ExtractLineColSpecAux2();
    while i < |input| && input[i] !in "\r\n"
      invariant 0 <= startLinePos <= i <= |input|
      invariant 
        ToCodeLocation(ExtractLineColSpecAux2(
          ExtractLineMutableState(input, pos, startLinePos, i, lineNumber, colNumber)))
        == ExtractLineCol(input, pos)
    {
      assert 
        ToCodeLocation(ExtractLineColSpecAux2(
          ExtractLineMutableState(input, pos, startLinePos, i + 1, lineNumber, colNumber)))
        == ExtractLineCol(input, pos);
      i := i + 1;
    }
    assert ExtractLineCol(input, pos) == ToCodeLocation(ExtractLineMutableState(input, pos, startLinePos, i, lineNumber, colNumber));
    lineStr := input[startLinePos..i];
    output := CodeLocation(lineNumber, colNumber, lineStr);
    reveal ToCodeLocation();
    assert ExtractLineCol(input, pos) == output;
  }

  function DebugSummary(input: string): string {
    IntToString(|input|) + " \"" +
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
      print "| R: ", DebugSummary(A.View(result.Remaining()));
      if A.Length(result.Remaining()) < |input| {
        print "| Was committed\n";
      }
      print "| " + NewIndent(FailureToString(input, result), "| "), "\n";
    } else {
      print " (Success)\n";
    }
  }

  opaque function FailureToString<R>(input: string, result: ParseResult<R>, printPos: int := -1): (failure: string)
    // Util to print the line, the column, and all the error messages
    // associated to a given parse failure
    requires result.Failure?
    decreases result.data
  {
    var failure := "";
    var failure := failure +
      if printPos == -1 then
        (if result.level == Fatal then "Fatal error" else "Error") + ":\n"
      else "";
    var pos: int := |input| - A.Length(result.data.remaining); // Need the parser to be Valid()
    var pos :=
      if pos < 0 then // Could be proved false if parser is Valid()
        0
      else
        pos;
    var failure :=
    if printPos == pos then failure else
      var output := ExtractLineCol(input, pos);
      var CodeLocation(line, col, lineStr) := output;
      failure + IntToString(line) + ": " + lineStr + "\n" +
      repeat_(" ", col + 2 + |IntToString(line)|) + "^" + "\n";
    var failure := failure + result.data.message;
    if result.data.next.Some? then
      var failure := failure + ", or\n";
      var subFailure := FailureToString<R>(input, Failure(result.level, result.data.next.value), pos);
      var failure := failure + subFailure;
      failure
    else
      var failure := failure + "\n";
      failure
  }
}