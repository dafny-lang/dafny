abstract module Std.Parsers.Core
// Functional parsers consuming sequences seq<C> from the left to the right.
// For parsers over strings, please refer to the StringParsers module
{
  import Wrappers

  export
    provides
      C, // The character type
      Wrappers, // Imported module
      Valid,
      Succeed,
      Epsilon,
      Fail,
      EndOfString,
      Bind,
      BindSucceeds,
      BindResult,
      Map,
      Not,
      And,
      Or,
      OrSeq,
      Lookahead,
      ?,
      If,
      Maybe,
      ConcatMap,
      Concat,
      ConcatL,
      ConcatR,
      Debug,
      Rep,
      RepSep,
      RepMerge,
      RepSepMerge,
      CharTest,
      ZeroOrMore,
      OneOrMore,
      Recursive,
      RecursiveMap,
      intToString,
      digitToInt,
      stringToInt,
      ParseResult.IsFailure,
      ParseResult.PropagateFailure,
      ParseResult.Extract
    reveals
      Parser,
      ParserSelector,
      Option, // From Wrappers
      FailureLevel,
      ParseResult,
      FailureData,
      RecursiveDef

  export All reveals *

  type C(!new, ==)
  // The character of the sequence being parsed

  type Parser<+R> = seq<C> -> ParseResult<R>
  // A parser is a total function from a position to a parse result
  // Because it returns a delta pos, it cannot return a position negative from the origing
  // If the parsing is out of context, it will return a failure.

  type ParserSelector<!R> = string -> Parser<R>
  // A parser selector is a function that, given a name that exists,
  // returns a parser associated to this name

  type Option<T> = Wrappers.Option<T>
  // The common option type, synonym definition

  datatype FailureData =
    FailureData(
      message: string,
      remaining: seq<C>,
      next: Option<FailureData>)
  // A Parser failure can mention several places
  // (e.g. which could have continued to parse)
  {
    function Concat(other: FailureData): FailureData
      // Concatenates two failure datas, the first staying in the front
    {
      if next == Option.None then
        this.(next := Option.Some(other))
      else
        FailureData(message, remaining, Option.Some(next.value.Concat(other)))
    }
  }

  datatype FailureLevel =
    // Failure level for parse results.
    // A Fatal error results in a unique FailurePosition
    // and will be propagated to the top ASAP
    // A Recoverable error can typically be processed.
    // Comittedness of the parser only depends if the .Remaining()
    // of the parse result has moved since the input was provided.
    Fatal | Recoverable

  datatype ParseResult<+R> =
      // ParseResult is the type of what a parser taking a seq<C> would return
    | Failure(level: FailureLevel, data: FailureData)
      // Returned if a parser failed.
    | Success(result: R, remaining: seq<C>)
  // Returned if a parser succeeds, with the increment in the position
  {
    function Remaining(): seq<C>
      // If Remaining() is the same as the input, the parser is "uncommitted",
      // which means combinators like Or and ZeroOrMore can try alternatives
    {
      if Success? then remaining else data.remaining
    }

    predicate IsFailure() {
      Failure?
    }

    predicate IsFatalFailure() {
      Failure? && level == Fatal
    }

    predicate IsFatal()
      requires IsFailure()
    {
      level == Fatal
    }

    function PropagateFailure<U>(): ParseResult<U>
      requires IsFailure()
    {
      Failure(level, data)
    }

    function Extract(): (R, seq<C>)
      requires !IsFailure()
    {
      (result, remaining)
    }

    function Map<R'>(f: R -> R'): ParseResult<R'>
      // Transforms the result of a successful parse result
    {
      match this
      case Success(result, remaining) =>
        Success(f(result), remaining)
      case Failure(level, data) =>
        Failure(level, data)
    }

    function MapRecoverableError(
      f: FailureData -> FailureData
    ): ParseResult<R>
      // If the result is a recoverable error,
      // let the function process it
    {
      match this
      case Failure(Recoverable, data) =>
        Failure(Recoverable, f(data))
      case _ => this
    }

    predicate NeedsAlternative(input: seq<C>)
      // Returns true if the parser result
      // - Is a failure
      // - Is recoverable
      // - Did not consume any input (not-committed)
    {
      Failure? && level == Recoverable && input == Remaining()
    }
  }

  predicate IsRemaining(input: seq<C>, remaining: seq<C>)
    // True if remaining is a suffix of the input
  {
    && |remaining| <= |input|
    && input[|input|-|remaining|..] == remaining
  }

  opaque ghost predicate Valid<R>(underlying: Parser<R>)
    // A parser is valid iff for any input, it never returns a fatal error
    // and always returns a suffix of its input
  {
    forall input: seq<C> ::
      && (underlying(input).Failure? ==> underlying(input).level == Recoverable)
      && IsRemaining(input, underlying(input).Remaining())
  }

  // ########################################
  // Parser combinators.
  // The following functions make it possible to create and compose parsers
  // All these combinators provide Valid() parsers if their inputs are Valid() too
  // ########################################

  opaque function Succeed<R>(result: R): (p: Parser<R>)
    // A parser that does not consume any input and returns the given value
  {
    (input: seq<C>) => Success(result, input)
  }

  opaque function Epsilon(): (p: Parser<()>)
    // A parser that always succeeds, consumes nothing and returns ()
  {
    Succeed(())
  }

  opaque function Fail<R>(message: string, level: FailureLevel := Recoverable): Parser<R>
    // A parser that does not consume any input and returns the given failure
  {
    (input: seq<C>) => Failure(level, FailureData(message, input, Option.None))
  }

  opaque function Result<R>(result: ParseResult<R>): Parser<R>
    // A parser that always returns the given result
  {
    (input: seq<C>) => result
  }

  opaque function EndOfString(): Parser<()>
    // A parser that fails if the string has not been entirely consumed
  {
    (input: seq<C>) =>
      if |input| == 0 then Success((), input)
      else Failure(Recoverable, FailureData("expected end of string", input, Option.None))
  }

  opaque function Bind<L, R>(
    left: Parser<L>,
    right: L -> Parser<R>
  ) : (p: Parser<R>)
    // Fails if the left parser fails.
    // If the left parser succeeds, provides its result and the remaining sequence
    // to the right parser generator.
    // For a more general version, look at BindSucceeds
  {
    (input: seq<C>)
    =>
      var (leftResult, remaining) :- left(input);
      right(leftResult)(remaining)
  }

  opaque function BindSucceeds<L, R>(
    left: Parser<L>,
    right: (L, seq<C>) -> Parser<R>
  ) : (p: Parser<R>)
    // Fails if the left parser fails.
    // If the left parser succeeds, provides its result and its remaining
    // to the right parser generator and returns its result applied to the remaining
    // For a more general version, look at BindResult
  {
    (input: seq<C>)
    =>
      var (leftResult, remaining) :- left(input);
      right(leftResult, remaining)(remaining)
  }

  opaque function BindResult<L, R>(
    left: Parser<L>,
    right: (ParseResult<L>, seq<C>) -> Parser<R>
  ) : (p: Parser<R>)
    // Given a left parser and a parser generator based on the output
    // of the left parser,
    // returns the result of the right parser applied on the original input
  {
    (input: seq<C>)
    =>
      right(left(input), input)(input)
  }

  opaque function Map<R, U>(underlying: Parser<R>, mappingFunc: R -> U)
    : (p: Parser<U>)
    // A parser combinator that makes it possible to transform the result of a parser in another one
    // The mapping function can be partial
    // ensures forall pos | MapSpec(size, underlying, mappingFunc, pos) ::
    //          p.requires(pos)
  {
    (input: seq<C>) =>
      var (result, remaining) :- underlying(input);
      var u := mappingFunc(result);
      Success(u, remaining)
  }

  opaque function Not<R>(underlying: Parser<R>): Parser<()>
    // Returns a parser that succeeds if the underlying parser fails
    // and vice-versa. The result does not consume any input
  {
    (input: seq<C>) =>
      var l := underlying(input);
      if l.IsFailure() then
        if l.IsFatal() then l.PropagateFailure()
        else Success((), input)
      else Failure(Recoverable, FailureData("not failed", input, Option.None))
  }

  opaque function And<L, R>(
    left: Parser<L>,
    right: Parser<R>
  ) : (p: Parser<(L, R)>)
    // Make the two parsers parse the same string and, if both suceed,
    // returns a pair of the two results, with the remaining of the right
  {
    (input: seq<C>) =>
      var (l, remainingLeft) :- left(input);
      var (r, remainingRight) :- right(input);
      Success((l, r), remainingRight)
  }

  opaque function Or<R>(
    left: Parser<R>,
    right: Parser<R>
  ) : (p: Parser<R>)
    // left parses the string. If left succeeds, returns
    // if left fails, two cases
    // - If the error is recoverable and the parser did not consume input,
    //   then return what right returns
    // - Otherwise return both errors
  {
    (input: seq<C>) =>
      var p := left(input);
      if !p.NeedsAlternative(input) then p else
      var p2 := right(input);
      if !p2.NeedsAlternative(input) then p2 else
      p2.MapRecoverableError(
        dataRight =>
          p.data.Concat(dataRight))
  }

  opaque function OrSeq<R>(
    alternatives: seq<Parser<R>>
  ): Parser<R>
  {
    if |alternatives| == 0 then Fail("no alternatives") else
    if |alternatives| == 1 then alternatives[0]
    else
      Or(alternatives[0], OrSeq(alternatives[1..]))
  }

  opaque function Lookahead<R>(underlying: Parser<R>): (p: Parser<R>)
    // If the underlying parser succeeds,
    //   returns its result without committing the input
    // if the underlying parser fails,
    // - If the failure is fatal, returns it as-it
    // - If the failure is recoverable, returns it without comitting the input
  {
    (input: seq<C>) =>
      var p := underlying(input);
      if p.IsFailure() then
        if p.IsFatal() then
          p
        else
          p.(data := FailureData(p.data.message, input, Option.None))
      else
        p.(remaining := input)
  }

  opaque function ?<R>(underlying: Parser<R>): (p: Parser<R>)
    // Like Lookahead, except that if the parser succeeds,
    //   it keeps the committedness of the input.
    // Identical to Lookahead, if the underlying parser fails,
    // - If the failure is fatal, returns it as-it
    // - If the failure is recoverable, returns it without comitting the input
  {
    (input: seq<C>) =>
      var p := underlying(input);
      if p.IsFailure() then
        if p.IsFatal() then
          p
        else
          p.(data := FailureData(p.data.message, input, Option.None))
      else
        p
  }

  opaque function If<L, R>(
    condition: Parser<L>,
    succeed: Parser<R>
  ) : (p: Parser<R>)
    // If the condifition fails, returns a non-committing failure
    // Suitable to use in Or parsers
  {
    Bind(Lookahead(condition), (l: L) => succeed)
  }

  opaque function Maybe<R>(underlying: Parser<R>): Parser<Option<R>>
    // Transforms a recoverable failure into None,
    // and wraps a success into Some(...)
  {
    (input: seq<C>) =>
      var u := underlying(input);
      if u.IsFatalFailure() then u.PropagateFailure()
      else
      if u.Success? then u.Map(result => Option.Some(result))
      else Success(Option.None, input)
  }

  opaque function ConcatMap<L, R, T>(
    left: Parser<L>,
    right: Parser<R>,
    mapper: (L, R) -> T
  ) : (p: Parser<T>)
    // Apply two consecutive parsers consecutively
    // If both succeed, apply the mapper to the result and return it
  {
    (input: seq<C>)
    =>
      var (l, remaining) :- left(input);
      var (r, remaining2) :- right(remaining);
      Success(mapper(l, r), remaining2)
  }

  opaque function Concat<L, R>(
    left: Parser<L>,
    right: Parser<R>
  ) : (p: Parser<(L, R)>)
    // Apply two consecutive parsers consecutively
    // If both succeed, return the pair of the two results
  {
    (input: seq<C>) =>
      var (l, remaining) :- left(input);
      var (r, remaining2) :- right(remaining);
      Success((l, r), remaining2)
  }

  opaque function ConcatR<L, R>(
    left: Parser<L>,
    right: Parser<R>
  ) : (p: Parser<R>)
    // Return only the result of the right parser if the two parsers match
  {
    ConcatMap(left, right, (l, r) => r)
  }

  opaque function ConcatL<L, R>(
    left: Parser<L>,
    right: Parser<R>
  ) : (p: Parser<L>)
    // Return only the result of the right parser if the two parsers match
  {
    ConcatMap(left, right, (l, r) => l)
  }

  /** Use a function that can print to debug, and possibly modify the parser*/
  opaque function Debug<R, D>(underlying: Parser<R>, name: string, onEnter: (string, seq<C>) -> D, onExit: (string, D, ParseResult<R>) -> ()): (p: Parser<R>) {
    (input: seq<C>) =>
      var debugData := onEnter(name, input);
      var output := underlying(input);
      var _ := onExit(name, debugData, output);
      output
  }

  opaque function ZeroOrMore<R>(
    underlying: Parser<R>
  ): Parser<seq<R>>
    // Repeats the underlying parser until the first failure
    // that accepts alternatives, and returns the underlying sequence
  {
    Rep(underlying, (result: seq<R>, r: R) => result + [r], [])
  }

  opaque function OneOrMore<R>(underlying: Parser<R>): (p: Parser<seq<R>>)
    // Repeats the underlying parser until the first failure
    // Will return a failure if there is not at least one match
  {
    Bind(underlying, (r: R) =>
           Rep(underlying, (s: seq<R>, r': R) => s + [r'], [r]))
  }

  opaque function Rep<A, B>(
    underlying: Parser<B>,
    combine: (A, B) -> A,
    acc: A
  ): Parser<A>
    // Repeats the underlying parser until the first failure
    // that accepts alternatives, combining results to an accumulator
    // and return the final accumulator
  {
    (input: seq<C>) => Rep_(underlying, combine, acc, input)
  }

  opaque function RepSep<A, B>(
    underlying: Parser<A>,
    separator: Parser<B>
  ): Parser<seq<A>>
    // Repeats the underlying parser interleaved with a separator
    // Returns a sequence of results
  {
    Bind(Maybe(underlying), (result: Option<A>) =>
           if result.None? then Succeed<seq<A>>([]) else
           Rep(ConcatR(separator, underlying), (acc: seq<A>, a: A) => acc + [a], [result.value]))
  }

  opaque function RepMerge<A>(
    underlying: Parser<A>,
    merger: (A, A) -> A
  ): Parser<A>
    // Repeats the underlying parser interleaved with a separator
    // Returns a sequence of results
  {
    Bind(Maybe(underlying), (result: Option<A>) =>
           if result.None? then Fail<A>("No first element in RepMerge", Recoverable) else
           Rep(underlying, (acc: A, a: A) => merger(acc, a), result.value))
  }

  opaque function RepSepMerge<A, B>(
    underlying: Parser<A>,
    separator: Parser<B>,
    merger: (A, A) -> A
  ): Parser<A>
    // Repeats the underlying parser interleaved with a separator
    // Returns a sequence of results
  {
    Bind(Maybe(underlying), (result: Option<A>) =>
           if result.None? then Fail<A>("No first element in RepSepMerge", Recoverable) else
           Rep(ConcatR(separator, underlying), (acc: A, a: A) => merger(acc, a), result.value))
  }

  opaque function {:tailrecursion true} Rep_<A, B>(
    underlying: Parser<B>,
    combine: (A, B) -> A,
    acc: A,
    input: seq<C>
  ): (p: ParseResult<A>)
    decreases |input|
    // ZeroOrMore the underlying parser over the input until a recoverable failure happens
    // and returns the accumulated results
  {
    match underlying(input)
    case Success(result, remaining) =>
      if |remaining| >= |input| then Success(acc, input) else
      Rep_(underlying, combine, combine(acc, result), remaining)
    case failure =>
      if failure.NeedsAlternative(input) then
        Success(acc, input)
      else
        failure.PropagateFailure()
  }

  opaque function Recursive<R(!new)>(
    underlying: Parser<R> -> Parser<R>
  ): (p: Parser<R>)
    // Given a function that requires a parser to return a parser,
    // provide the result of this parser to that function itself.
    // Careful: This function is not tail-recursive and will consume stack.
    // Prefer using Rep() or ZeroOrMore() for sequences
  {
    (input: seq<C>) => Recursive_(underlying, input)
  }

  opaque function Recursive_<R(!new)>(
    underlying: Parser<R> -> Parser<R>,
    input: seq<C>
  ): (p: ParseResult<R>)
    // Implementation for Recursive()
    decreases |input|
  {
    var callback: Parser<R> :=
      (remaining: seq<C>) =>
        if |remaining| < |input| then
          Recursive_(underlying, remaining)
        else if |remaining| == |input| then
          Failure(Recoverable, FailureData("no progress", remaining, Option.None))
        else
          Failure(Fatal, FailureData("fixpoint called with an increasing remaining sequence", remaining, Option.None));
    underlying(callback)(input)
  }

  opaque function RecursiveMap<R(!new)>(
    underlying: map<string, RecursiveDef<R>>,
    fun: string): (p: Parser<R>)
    // Given a map of name := recursive definitions,
    // provide the result of this parser to the recursive definitions
    // and set 'fun' as the initial parser.
    // Careful: This function is not tail-recursive and will consume stack
  {
    (input: seq<C>) => RecursiveMap_(underlying, fun, input)
  }

  datatype RecursiveDef<!R> = RecursiveDef(
    order: nat,
    definition: ParserSelector<R> -> Parser<R>
  ) // The order must be decreasing every time the function steps in
  // But it can jump to a bigger order if the input is consumed

  opaque function RecursiveMap_<R(!new)>(
    underlying: map<string, RecursiveDef<R>>,
    fun: string,
    input: seq<C>
  ): (p: ParseResult<R>)
    // Implementation for RecursiveMap()
    decreases |input|, if fun in underlying then underlying[fun].order else 0
  {
    if fun !in underlying then Failure(Fatal, FailureData("parser '"+fun+"' not found", input, Option.None)) else
    var RecursiveDef(orderFun, definitionFun) := underlying[fun];
    var callback: ParserSelector<R>
      :=
      (fun': string) =>
        (var p : Parser<R> :=
           if fun' !in underlying.Keys then
             Fail(fun' + " not defined", Fatal)
           else
             var RecursiveDef(orderFun', definitionFun') := underlying[fun'];
             (remaining: seq<C>) =>
               if |remaining| < |input| || (|remaining| == |input| && orderFun' < orderFun) then
                 RecursiveMap_(underlying, fun', remaining)
               else if |remaining| == |input| then
                 Failure(Recoverable, FailureData("non-progressing recursive call requires that order of '"
                                                  +fun'+"' ("+intToString(orderFun')+") is lower than the order of '"+fun+"' ("+intToString(orderFun)+")", remaining, Option.None))
               else
                 Failure(Fatal, FailureData("parser did not return a suffix of the input", remaining, Option.None))
           ; p);
    definitionFun(callback)(input)
  }

  opaque function CharTest(test: C -> bool, name: string): (p: Parser<C>)
    // A parser that returns the current char if it passes the test
    // Returns a recoverable error based on the name otherwise
  {
    (input: seq<C>) =>
      if 0 < |input| && test(input[0]) then Success(input[0], input[1..])
      else Failure(Recoverable,
                   FailureData("expected a "+name, input, Option.None))
  }

  opaque function intToString(n: int): string
    // Converts an integer to a string
    decreases if n < 0 then 1 - n else n
  {
    if n < 0 then "-" + intToString(-n) else
    match n
    case 0 => "0" case 1 => "1" case 2 => "2" case 3 => "3" case 4 => "4"
    case 5 => "5" case 6 => "6" case 7 => "7" case 8 => "8" case 9 => "9"
    case _ => intToString(n / 10) + intToString(n % 10)
  }

  opaque function digitToInt(c: char): int {
    match c
    case '0' => 0 case '1' => 1 case '2' => 2 case '3' => 3 case '4' => 4
    case '5' => 5 case '6' => 6 case '7' => 7 case '8' => 8 case '9' => 9
    case _ => -1
  }

  opaque function stringToInt(s: string): int
    // Converts a string to a string
    decreases |s|
  {
    if |s| == 0 then 0 else
    if |s| == 1 then digitToInt(s[0])
    else if s[0] == '-' then
      0 - stringToInt(s[1..])
    else
      stringToInt(s[0..|s|-1])*10 + stringToInt(s[|s|-1..|s|])
  }
}