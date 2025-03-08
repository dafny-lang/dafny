// A parser that can parse a JSON-like structure
// Strings however are parsed without unicode escape.
module ExampleParsers.JSONParser {
  import opened Std.Parsers.StringBuilders
  datatype Decimal =
    Decimal(n: int, e10: int) // (n) * 10^(e10)

  function ToDecimal(n: int): Decimal {
    Decimal(n, 0)
  }

  function ToDecimalFrac(n: int, digits: seq<nat>, e10: int := 0): Decimal
    decreases |digits|
  {
    if digits == [] then Decimal(n, e10)
    else ToDecimalFrac(n * 10 + digits[0], digits[1..], e10 - 1)
  }

  datatype JSON =
    | Null
    | Bool(b: bool)
    | String(str: string)
    | Number(num: Decimal)
    | Object(obj: seq<(string, JSON)>) // Not a map to preserve order
    | Array(arr: seq<JSON>)

  const nullParser: B<JSON> := WS().e_I(S("null")).??().M((s) => Null)
  const boolParser: B<JSON> := WS().e_I(O([S("true"), S("false")])).??().M((s: string) =>
                                                                             Bool(s == "true"))
  const stringCharParser: B<string> :=
    O([
        S("\\\"").??().M((s: string) => '"'),
        S("\\\\").??().M((s: string) => '\\'),
        CharTest((c: char) => c != '\\' && c != '"', "no escape no quote"
        ).??()
      ]).ZeroOrMore()

  const stringParser: B<string> := WS().e_I(S("\"")).??().e_I(stringCharParser).I_e(S("\""))

  const stringJSONParser: B<JSON> := stringParser.M((s: string) => String(s))

  const numberJSONParser: B<JSON> :=
    Int().I_I(S(".").e_I(DigitNumber().ZeroOrMore()).?()).M(
      (s: (int, P.Option<seq<nat>>)) =>
        if s.1.None? then Number(ToDecimal(s.0))
        else Number(ToDecimalFrac(s.0, s.1.value, 0)))

  const arrayParser: B<JSON> -> B<JSON> := (rec: B<JSON>) =>
    WS().e_I(S("[")).??().e_I(
      WS().e_I(rec).RepSep(WS().e_I(S(","))).M((s: seq<JSON>) => Array(s))
      .I_e(WS()).I_e(S("]")))

  const objectParser: B<JSON> -> B<JSON> := (rec: B<JSON>) =>
    WS().e_I(S("{")).??().e_I(
      WS().e_I(stringParser).I_I(WS().e_I(S(":").e_I(WS()).e_I(rec)))
      .RepSep(WS().e_I(S(","))).M((s: seq<(string, JSON)>) => Object(s))
      .I_e(WS()).I_e(S("}")))

  const parseProgram: B<JSON> :=
    Rec((rec: B<JSON>) =>
          O([
              nullParser,
              boolParser,
              stringJSONParser,
              numberJSONParser,
              arrayParser(rec),
              objectParser(rec)
            ])).I_e(End())

  method {:test} TestParser() {
    var source := @"{""a"": null, ""b"": [1.42, 25.150]}";
    expect parseProgram.apply(source)
        == P.Success(JSON.Object([(['a'], JSON.Null), (['b'], JSON.Array([JSON.Number(Decimal.Decimal(142, -2)), JSON.Number(Decimal.Decimal(25150, -3))]))]), "");
    expect parseProgram.apply("[  ]")
        == P.Success(JSON.Array([]), "");
    expect parseProgram.apply(@"[true, false, null]")
        == P.Success(JSON.Array([JSON.Bool(true), JSON.Bool(false), JSON.Null]), "");
  }
}