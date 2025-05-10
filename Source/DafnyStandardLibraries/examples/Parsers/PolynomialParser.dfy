/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/** Definition of a single-variable polynomial expression */
module ExampleParsers.Polynomial {
  import opened Std.Wrappers
  import Std.Strings

  datatype Expr =
    | Binary(op: string, left: Expr, right: Expr) // left op right
    | Number(value: int)                          // a constant
    | Unknown(power: int)                         // x^power
  {
    function Simplify(): Result<Expr, string> {
      match this {
        case Number(x: int) => Result.Success(this)
        case Binary(op, left, right) =>
          var l :- left.Simplify();
          var r :- right.Simplify();
          if l.Number? && r.Number? then
            match op {
              case "+" => Result.Success(Number(l.value + r.value))
              case "-" => Result.Success(Number(l.value - r.value))
              case "*" => Result.Success(Number(l.value * r.value))
              case "/" =>
                if r.value == 0 then
                  Result.Failure("Division by zero (" + right.ToString()
                                 + " evaluates to zero)")
                else
                  Result.Success(Number(l.value / r.value))
              case "%" =>
                if r.value == 0 then
                  Result.Failure("Modulo by zero (" + right.ToString()
                                 + " evaluates to zero)")
                else
                  Result.Success(Number(l.value % r.value))
              case _ => Result.Failure("Unsupported operator: " + op)
            }
          else
            Result.Success(Binary(op, l, r))
        case Unknown(0) => Result.Success(Number(1))
        case Unknown(_) => Result.Success(this)
      }
    }
    static function InfixBuilder(): (Expr, (string, Expr)) -> Expr
    {
      (left: Expr, right: (string, Expr)) => Binary(right.0, left, right.1)
    }
    function ToString(): string {
      match this
      case Number(x) => Strings.OfInt(x)
      case Binary(op, left, right) =>
        "("
        + left.ToString() + op + right.ToString()
        + ")"
      case Unknown(power) =>
        if power == 1 then "x" else if power == 0 then "1" else
        "x^" + Strings.OfInt(power)
    }
  }
}

/** An abstract module to parse polynomials */
abstract module ExampleParsers.TestPolynomialParser {
  import opened Polynomial
  type UnderlyingParser<T>
  type ParseResult<T>
  function PolynomialParser(): UnderlyingParser<Expr>

  function Parse<T>(parser: UnderlyingParser<T>, input: string): ParseResult<T>
  predicate IsSuccess<T>(p: ParseResult<T>)
  function Extract<T>(p: ParseResult<T>): T
    requires IsSuccess(p)
  function FailureToString<T>(input: string, p: ParseResult<T>): string
    requires !IsSuccess(p)

  method TestSimplify(input: string, expectedSimplified: string) {
    var x := Parse(PolynomialParser(), input);
    if !IsSuccess(x) {
      print FailureToString(input, x), "\n";
    }
    expect IsSuccess(x);
    var xSimplified := Extract(x).Simplify();
    expect xSimplified.Success?;
    var inputSimplified := xSimplified.value.ToString();
    if inputSimplified != expectedSimplified {
      print "Expected:\n", expectedSimplified, "\ngot:\n", inputSimplified, "\n";
      expect inputSimplified == expectedSimplified;
    }
  }

  method TestPolynomialCommon() {
    TestSimplify("2+3*4", "14");
    TestSimplify("(2+3)*4", "20");
    TestSimplify("3*4+2", "14");
    TestSimplify("3*(4+2)", "18");
    TestSimplify("(1+2)*x", "(3*x)");
    TestSimplify("(1+2)*x", "(3*x)");
    TestSimplify("((50%40)/2-1)*x^3", "(4*x^3)");
  }
}

/** Recursive and terminating parser of polynomial expressions */
module ExampleParsers.PolynomialParsersBuilder refines TestPolynomialParser {
  import opened Std.Parsers.StringBuilders
  type UnderlyingParser<T> = B<T>
  type ParseResult<T> = P.ParseResult<T>
  function PolynomialParser(): UnderlyingParser<Expr> {
    parser
  }
  function Parse<T>(parser: UnderlyingParser<T>, input: string): ParseResult<T> {
    Apply(parser, input)
  }
  predicate IsSuccess<T>(p: ParseResult<T>) {
    p.ParseSuccess?
  }
  function Extract<T>(p: ParseResult<T>): T  {
    p.result
  }
  function FailureToString<T>(input: string, p: ParseResult<T>): string
  {
    P.FailureToString(input, p)
  }

  // Parsers builder style
  const parser: B<Expr>
    :=
    RecMap(
      map[
        "atom" := RecMapDef(
          0, (c: RecMapSel<Expr>) =>
            O([
                S("(").e_I(c("term")).I_e(S(")")),
                Int.M((result: int) => Number(result)),
                S("x").e_I(S("^").e_I(Int).?().M(
                             (result: P.Option<int>) =>
                               if result.Some? then Unknown(result.value) else Unknown(1)))
              ])),

        "factor" := RecMapDef(
          1, (c: RecMapSel<Expr>) =>
            c("atom").Then(
              (atom: Expr) =>
                O([S("*"), S("/"), S("%")])
                .I_I(c("atom")).RepFold(atom, Expr.InfixBuilder()))),

        "term" := RecMapDef(
          2, (c: RecMapSel<Expr>) =>
            c("factor").Then(
              (atom: Expr) =>
                O([S("+"), S("-")])
                .I_I(c("factor")).RepFold(atom, Expr.InfixBuilder())))
      ], "term")
    .End()

  @Test
  method TestPolynomial() {
    TestPolynomialCommon();
  }
}

// Same as above, but using the Parsers functional syntax instead of the builder syntax
module ExampleParsers.PolynomialParsers refines TestPolynomialParser {
  import opened P = Std.Parsers.StringBuilders.P
  type UnderlyingParser<T> = Parser<T>
  type ParseResult<T> = P.ParseResult<T>
  function PolynomialParser(): UnderlyingParser<Expr> {
    parser
  }
  function Parse<T>(parser: UnderlyingParser<T>, input: string): ParseResult<T> {
    Apply(parser, input)
  }
  predicate IsSuccess<T>(p: ParseResult<T>) {
    p.ParseSuccess?
  }
  function Extract<T>(p: ParseResult<T>): T  {
    p.result
  }
  function FailureToString<T>(input: string, p: ParseResult<T>): string
  {
    P.FailureToString(input, p)
  }

  // Parser combinators style
  const parser: Parser<Expr>
    := ConcatKeepLeft(
         RecursiveMap(
           map[
             "atom" := RecursiveDef(
               0, (callback: ParserSelector<Expr>) =>
                 Or(ConcatKeepRight(
                      String("("), ConcatKeepLeft(
                        callback("term"),
                        String(")"))),
                    Or(
                      Map(Int(), (result: int) => Number(result)), ConcatKeepRight(
                        String("x"),
                        Map(Maybe(ConcatKeepRight(
                                    String("^"), Int())),
                            (result: Option<int>) =>
                              if result.Some? then Unknown(result.value) else Unknown(1)
                        ))))),
             "factor" := RecursiveDef(
               1, (callback: ParserSelector<Expr>) =>
                 Bind(callback("atom"), (atom: Expr) =>
                        Rep(
                          Concat(Or(String("*"), Or(String("/"), String("%"))),
                                 callback("atom")),
                          Expr.InfixBuilder(), atom)
                 )),

             "term" := RecursiveDef(
               2, (callback: ParserSelector<Expr>) =>
                 Bind(callback("factor"), (factor: Expr) =>
                        Rep(
                          Concat(Or(String("+"), String("-")),
                                 callback("factor")),
                          Expr.InfixBuilder(), factor)
                 ))
           ], "term"), EndOfString())

  @Test
  method TestPolynomial() {
    TestPolynomialCommon();
  }
}
