module ExampleParsers.PolynomialParser {
  import opened P = Std.Parsers.StringBuilders.P
  // Parser combinators style
  const parser: Parser<Expr>
    := ConcatL(
         RecursiveMap(
           map[
             "atom" := RecursiveDef(
               0, (callback: ParserSelector<Expr>) =>
                 Or(ConcatR(
                      String("("), ConcatL(
                        callback("term"),
                        String(")"))),
                    Or(
                      Map(Int(), (result: int) => Number(result)), ConcatR(
                        String("x"),
                        Map(Maybe(ConcatR(
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

  type Result<A, B> = Wrappers.Result<A, B>

  datatype Expr =
    | Binary(op: string, left: Expr, right: Expr)
    | Number(value: int)
    | Unknown(power: int)
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
      case Number(x) => P.IntToString(x)
      case Binary(op, left, right) =>
        "("
        + left.ToString() + op + right.ToString()
        + ")"
      case Unknown(power) =>
        if power == 1 then "x" else if power == 0 then "1" else
        "x^" + P.IntToString(power)
    }
  }

  method TestSimplify(input: string, expectedSimplified: string) {
    var x := Apply(parser, input);
    if !x.ParseSuccess? {
      print FailureToString(input, x), "\n";
    }
    expect x.ParseSuccess?;
    var xSimplified := x.result.Simplify();
    expect xSimplified.Success?;
    var inputSimplified := xSimplified.value.ToString();
    if inputSimplified != expectedSimplified {
      print "Expected:\n", expectedSimplified, "\ngot:\n", inputSimplified, "\n";
      expect inputSimplified == expectedSimplified;
    }
  }

  @Test
  method TestPolynomial() {
    TestSimplify("2+3*4", "14");
    TestSimplify("(2+3)*4", "20");
    TestSimplify("3*4+2", "14");
    TestSimplify("3*(4+2)", "18");
    TestSimplify("(1+2)*x", "(3*x)");
    TestSimplify("(1+2)*x", "(3*x)");
    TestSimplify("((50%40)/2-1)*x^3", "(4*x^3)");
  }

  @Print
  method Main(args: seq<string>) {
    if |args| <= 1 {
      print "Please provide a polynomial to parse as argument\n";
      return;
    }
    for i := 1 to |args| {
      var input := args[i];
      match Apply(parser, input) {
        case ParseSuccess(result, remaining) =>
          print "Polynomial:", result.ToString(), "\n";
          match result.Simplify() {
            case Success(x) =>
              print "Simplified:", x.ToString(), "\n";
            case Failure(message) =>
              print message;
          }
        case failure =>
          print FailureToString(input, failure);
      }
      print "\n";
    }
  }
}