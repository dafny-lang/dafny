module Std.Parsers.StringBuilders refines Builders {
  import P = StringParsers
  export StringBuilders extends Builders
    provides S, Int, Nat, WS, Except, Digit, DigitNumber, DebugSummaryInput, PrintDebugSummaryOutput, FailureToString, Apply

  function S(s: string): B<string> {
    B(P.String(s))
  }
  function Int(): B<int> {
    B(P.Int())
  }
  function Nat(): B<nat> {
    B(P.Nat())
  }
  function Digit(): B<char> {
    B(P.Digit())
  }
  function DigitNumber(): B<nat> {
    B(P.DigitNumber())
  }
  function WS(): B<string> {
    B(P.WS())
  }
  function Except(s: string): B<string> {
    B(P.ZeroOrMore(P.CharTest((c: char) => c !in s, s)))
  }
  function DebugSummaryInput(name: string, input: string): string {
    P.DebugSummaryInput(name, input)
  }
  method {:print} PrintDebugSummaryOutput<R>(name: string, input: string, result: P.ParseResult<R>) {
    P.PrintDebugSummaryOutput(name, input, result);
  }
  function FailureToString<R>(input: string, result: P.ParseResult<R>): (s: string)
    requires result.Failure?
  {
    P.FailureToString(input, result)
  }
  function Apply<T>(parser: B<T>, input: string): P.ParseResult<T> {
    parser.apply(P.A.Input(input, 0, |input|))
  }
}