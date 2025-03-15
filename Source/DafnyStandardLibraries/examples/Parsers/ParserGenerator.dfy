// A small regex-like language that can be turned into a straightforward parser
// So first we parse the parser to ParserSpec, we convert it to a parser
// and we parse the string using this parser.
// Possible next step: Compile this parser and prove it does the same.
module ExampleParsers.ParserGenerator {
  import opened Std.Parsers.StringBuilders
  import opened Std.Wrappers

  function ToBool<T>(): T -> bool {
    t => true
  }

  datatype ParserSpec =
    | Const(s: string)
    | And(left: ParserSpec, right: ParserSpec)
    | Or(left: ParserSpec, right: ParserSpec)
    | Repeat(p: ParserSpec)
  {
    predicate OnlyAndRepeat() {
      match this
      case Const(s) => true
      case And(left, right) => left.OnlyAndRepeat() && right.OnlyAndRepeat()
      case Or(left, right) => false
      case Repeat(p) => p.OnlyAndRepeat()
    }
    function ToParser(): B<bool> {
      match this
      case Const(s) => S(s).M(ToBool())
      case And(left, right) => left.ToParser().e_I(right.ToParser()).M(ToBool())
      case Or(left, right) => O([left.ToParser().??(), right.ToParser()]).M(ToBool())
      case Repeat(x) => x.ToParser().??().Rep().M(ToBool())
    }
    function ToString(): string {
      match this
      case Const(s) => s
      case And(left, right) => left.ToString() + right.ToString()
      case Or(left, right) => "(" + left.ToString() + "|" + right.ToString() + ")"
      case Repeat(underlying) =>
        var u := underlying.ToString();
        if |u| == 0 then "" else
        if u[0..1] == "(" then u + "*"
        else "(" + u + ")*"
    }
  }

  const parseSpec: B<ParserSpec> :=
    RecMap(
      map[
        "atom" :=
          RecMapDef(
            0, (c: RecMapSel<ParserSpec>) =>
              O([
                  S("(").e_I(c("or")).I_e(S(")")).Then(
                    (atom: ParserSpec) =>
                      S("*").?().M((star: Option<string>) =>
                                     if star.None? then atom else Repeat(atom))
                  ),
                  Except("()|").M((r: string) => ParserSpec.Const(r))
                ])),
        "and" :=
          RecMapDef(
            1, (c: RecMapSel<ParserSpec>) =>
              c("atom").RepMerge((atom1: ParserSpec, atom2: ParserSpec) => And(atom1, atom2))),
        "or" :=
          RecMapDef(
            2, (c: RecMapSel<ParserSpec>) =>
              c("and").RepSepMerge(S("|"), (and1: ParserSpec, and2: ParserSpec) => Or(and1, and2)))
      ], "or")

  method {:test} TestParser() {
    var program := "abc((de|f((g))*))ml";
    var parser := parseSpec.Apply(program);
    expect parser.ParseSuccess?
           && parser.result.ToString() == "abc(de|f(g)*)ml";
    var underlying := parser.result.ToParser();
    program := "abcdeml";
    expect underlying.Apply(program) == ParseResult.ParseSuccess(true, ToInputEnd(program));
  }
}