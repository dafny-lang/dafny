module ExampleParsers.PolynomialParsersBuilder {
  import opened Std.Parsers.StringBuilders

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

  type Result<A, B> = P.Wrappers.Result<A, B>

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
      case Number(x) => IntToString(x)
      case Binary(op, left, right) =>
        "("
        + left.ToString() + op + right.ToString()
        + ")"
      case Unknown(power) =>
        if power == 1 then "x" else if power == 0 then "1" else
        "x^" + IntToString(power)
    }
  }

  method {:print} Main(args: seq<string>) {
    if |args| <= 1 {
      print "Please provide a polynomial to parse as argument\n";
      return;
    }
    for i := 1 to |args| {
      var input := args[i];
      match parser.Apply(input) {
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