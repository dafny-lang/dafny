/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/** A parser that can parse a JSON-like structure
  * Strings however are parsed without unicode escape. */
module ExampleParsers.JSONParser {
  import opened Std.Parsers.StringBuilders
  import opened Std.JSON.Values

  function ToDecimal(n: int): Decimal {
    Decimal(n, 0)
  }

  function ToDecimalFrac(n: int, digits: seq<nat>, e10: int := 0): Decimal
    decreases |digits|
  {
    if digits == [] then Decimal(n, e10)
    else ToDecimalFrac(n * 10 + digits[0], digits[1..], e10 - 1)
  }

  const nullParser: B<JSON> := S("null").M((s) => Null)
  const boolParser: B<JSON> := O([S("true"), S("false")]).M(
                                 (s: string) =>
                                   Bool(s == "true"))
  const stringCharParser: B<string> :=
    O([
        S("\\\"").M((s: string) => '"'),
        S("\\\\").M((s: string) => '\\'),
        CharTest((c: char) => c != '\\' && c != '"', "a character other than a backslash or a double quote")
      ]).Rep()

  const stringParser: B<string> := S("\"").e_I(stringCharParser).I_e(S("\""))

  const stringJSONParser: B<JSON> := stringParser.M((s: string) => String(s))

  const numberJSONParser: B<JSON> :=
    StringBuilders.Int.I_I(S(".").e_I(DigitNumber.Rep()).?()).M(
      (s: (int, P.Option<seq<nat>>)) =>
        if s.1.None? then Number(ToDecimal(s.0))
        else Number(ToDecimalFrac(s.0, s.1.value, 0)))

  const arrayParser: B<JSON> -> B<JSON> := (rec: B<JSON>) =>
    S("[").e_I(WS).e_I(
      rec.I_e(WS).RepSep(S(",").I_e(WS)))
    .I_e(S("]"))
    .M((s: seq<JSON>) => Array(s))

  const objectParser: B<JSON> -> B<JSON> := (rec: B<JSON>) =>
    S("{").e_I(WS).e_I(
      stringParser.I_I(WS.e_I(S(":").e_I(WS).e_I(rec))).I_e(WS)
      .RepSep(S(",").I_e(WS)))
    .I_e(S("}"))
    .M((s: seq<(string, JSON)>) => Object(s))

  const parseProgram: B<JSON> :=
    WS.e_I(
      Rec((rec: B<JSON>) =>
            O([
                nullParser,
                boolParser,
                stringJSONParser,
                numberJSONParser,
                arrayParser(rec),
                objectParser(rec)
              ]).I_e(WS)).End())

  @Test
  method TestParserSuccess() {
    var source := @"{""a"": null, ""b"": [1.42, 25.150]}";
    expect parseProgram.Apply(source)
        == ParseResult.ParseSuccess(
             JSON.Object(
               [ (['a'], JSON.Null),
                 (['b'], JSON.Array([JSON.Number(Decimal.Decimal(142, -2)),
                  JSON.Number(Decimal.Decimal(25150, -3))]))]),
             ToInputEnd(source));
    source := "[  ]";
    var p := parseProgram.Apply(source);
    expect parseProgram.Apply(source)
        == ParseResult.ParseSuccess(JSON.Array([]), ToInputEnd(source));
    source := @"[true, false, null]";
    expect parseProgram.Apply(source)
        == ParseResult.ParseSuccess(JSON.Array([JSON.Bool(true), JSON.Bool(false), JSON.Null]), ToInputEnd(source));
  }

  @Test
  method TestParserFailure() {
    var source := @"[3, [1.42, 25.1[]]}";
    var result := parseProgram.Apply(source);
    expect result.ParseFailure?;
    expect FailureToString(source, result)
        == @"Error:"                 + "\n" +
           @"1: [3, [1.42, 25.1[]]}" + "\n" +
           @"                  ^"    + "\n" +
           @"expected ']'"           + "\n";
    source := @"{""a"":"+"\n\n\n\n\n\n\n\n\n\n\n\n"+
    @"  k12}";
    result := parseProgram.Apply(source);
    expect result.ParseFailure?;
    expect FailureToString(source, result)
        == @"Error:"               + "\n" +
           @"13:   k12}"           + "\n" +
           @"      ^"              + "\n" +
           @"expected 'null', or"  + "\n" +
           @"expected 'true', or"  + "\n" +
           @"expected 'false', or"  + "\n" +
           @"expected '""', or"    + "\n" +
           @"expected a digit, or" + "\n" +
           @"expected '[', or"     + "\n" +
           @"expected '{'"         + "\n";
  }
}