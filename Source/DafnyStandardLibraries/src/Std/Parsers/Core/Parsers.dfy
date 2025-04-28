/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/** Definition of an parser's abstract input.
    It enforces a mapping from an input to a sequence of characters */
abstract module Std.Parsers.AbstractInput {
  type Input(!new,==)
  type C(!new, ==)
  function ToInput(r: seq<C>): (i: Input)
    ensures View(i) == r

  function View(self: Input): (r: seq<C>)
    ensures |View(self)| == Length(self)
  function Length(self: Input): nat
  function CharAt(self: Input, i: int): C
    requires 0 <= i < Length(self)
    ensures CharAt(self, i) == View(self)[i]
  function Drop(self: Input, start: int): Input
    requires 0 <= start <= Length(self)
    ensures View(self)[start..] == View(Drop(self, start))
    ensures start == 0 ==> Drop(self, start )== self
  function Slice(self: Input, start: int, end: int): Input
    requires 0 <= start <= end <= Length(self)
    ensures View(self)[start..end] == View(Slice(self, start, end))
  lemma AboutDrop(self: Input, a: int, b: int)
    requires 0 <= a <= Length(self)
    requires 0 <= b <= Length(self) - a
    ensures Drop(self, a + b) == Drop(Drop(self, a), b)
}

abstract module Std.Parsers.Core
// Functional parsers consuming sequences seq<C> from the left to the right.
// For parsers over strings, please refer to the StringParsers module
{
  import Wrappers
  import Strings

  export
    provides
      Wrappers, // Imported module
      SucceedWith,
      Epsilon,
      FailWith,
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
      ConcatKeepLeft,
      ConcatKeepRight,
      Debug,
      Rep,
      RepSep,
      RepMerge,
      RepSepMerge,
      ResultWith,
      CharTest,
      ZeroOrMore,
      OneOrMore,
      Recursive,
      RecursiveNoStack,
      RecursiveMap,
      DigitToInt,
      StringToInt,
      ParseResult.IsFailure,
      ParseResult.PropagateFailure,
      ParseResult.Extract,
      A // The abstract input
    reveals
      C, // The character type
      Input, // The sequence type
      Parser,
      ParserSelector,
      Option, // From Wrappers
      FailureLevel,
      ParseResult,
      FailureData,
      RecursiveDef,
      RecursiveNoStackResult,
      RecursiveProgressError

  export All reveals *

  import A : AbstractInput

  type C = A.C
  type Input = A.Input

  // The character of the sequence being parsed

  type Parser<+R> = Input -> ParseResult<R>
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
      remaining: Input,
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
    | ParseFailure(level: FailureLevel, data: FailureData)
      // Returned if a parser failed.
    | ParseSuccess(result: R, remaining: Input)
  // Returned if a parser succeeds, with the increment in the position
  {
    function Remaining(): Input
      // If Remaining() is the same as the input, the parser is "uncommitted",
      // which means combinators like Or and ZeroOrMore can try alternatives
    {
      if ParseSuccess? then remaining else data.remaining
    }

    predicate IsFailure() {
      ParseFailure?
    }

    predicate IsFatalFailure() {
      ParseFailure? && level == Fatal
    }

    predicate IsFatal()
      requires IsFailure()
    {
      level == Fatal
    }

    function PropagateFailure<U>(): ParseResult<U>
      requires IsFailure()
    {
      ParseFailure(level, data)
    }

    function Extract(): (R, Input)
      requires !IsFailure()
    {
      (result, remaining)
    }

    function Map<R'>(f: R -> R'): ParseResult<R'>
      // Transforms the result of a successful parse result
    {
      match this
      case ParseSuccess(result, remaining) =>
        ParseSuccess(f(result), remaining)
      case ParseFailure(level, data) =>
        ParseFailure(level, data)
    }

    function MapRecoverableError(
      f: FailureData -> FailureData
    ): ParseResult<R>
      // If the result is a recoverable error,
      // let the function process it
    {
      match this
      case ParseFailure(Recoverable, data) =>
        ParseFailure(Recoverable, f(data))
      case _ => this
    }

    predicate NeedsAlternative(input: Input)
      // Returns true if the parser result
      // - Is a failure
      // - Is recoverable
      // - Did not consume any input (not-committed)
    {
      ParseFailure? && level == Recoverable && input == Remaining()
    }
  }

  predicate IsRemaining(input: Input, remaining: Input)
    // True if remaining is a suffix of the input
  {
    && A.Length(remaining) <= A.Length(input)
    && A.Drop(input, A.Length(input)-A.Length(remaining)) == remaining
  }

  lemma IsRemainingTransitive(input: Input, remaining1: Input, remaining2: Input)
    requires IsRemaining(input, remaining1)
    requires IsRemaining(remaining1, remaining2)
    ensures IsRemaining(input, remaining2)
  {
    A.AboutDrop(input, A.Length(input)-A.Length(remaining1), A.Length(remaining1)-A.Length(remaining2));
  }

  // Cannot express this predicate if Input is allocated. Add once we accept quantification over unallocated objects
  // when they are allocated
  /*opaque ghost predicate Valid<R>(underlying: Parser<R>)
    // A parser is valid iff for any input, it never returns a fatal error
    // and always returns a suffix of its input
  {
    forall input: Input ::
      && (underlying(input).Failure? ==> underlying(input).level == Recoverable)
      && IsRemaining(input, underlying(input).Remaining())
  }*/

  // ########################################
  // Parser combinators.
  // The following functions make it possible to create and compose parsers
  // All these combinators provide Valid() parsers if their inputs are Valid() too
  // ########################################

  opaque function SucceedWith<R>(result: R): (p: Parser<R>)
    // A parser that does not consume any input and returns the given value
  {
    (input: Input) => ParseSuccess(result, input)
  }

  opaque function Epsilon(): (p: Parser<()>)
    // A parser that always succeeds, consumes nothing and returns ()
  {
    SucceedWith(())
  }

  opaque function FailWith<R>(message: string, level: FailureLevel := Recoverable): Parser<R>
    // A parser that does not consume any input and returns the given failure
  {
    (input: Input) => ParseFailure(level, FailureData(message, input, Option.None))
  }

  opaque function ResultWith<R>(result: ParseResult<R>): Parser<R>
    // A parser that always returns the given result
  {
    (input: Input) => result
  }

  opaque function EndOfString(): Parser<()>
    // A parser that fails if the string has not been entirely consumed
  {
    (input: Input) =>
      if A.Length(input) == 0 then ParseSuccess((), input)
      else ParseFailure(Recoverable, FailureData("expected end of string", input, Option.None))
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
    (input: Input)
    =>
      var (leftResult, remaining) :- left(input);
      right(leftResult)(remaining)
  }

  opaque function BindSucceeds<L, R>(
    left: Parser<L>,
    right: (L, Input) -> Parser<R>
  ) : (p: Parser<R>)
    // Fails if the left parser fails.
    // If the left parser succeeds, provides its result and its remaining
    // to the right parser generator and returns its result applied to the remaining
    // For a more general version, look at BindResult
  {
    (input: Input)
    =>
      var (leftResult, remaining) :- left(input);
      right(leftResult, remaining)(remaining)
  }

  opaque function BindResult<L, R>(
    left: Parser<L>,
    right: (ParseResult<L>, Input) -> Parser<R>
  ) : (p: Parser<R>)
    // Given a left parser and a parser generator based on the output
    // of the left parser,
    // returns the result of the right parser applied on the original input
  {
    (input: Input)
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
    (input: Input) =>
      var (result, remaining) :- underlying(input);
      var u := mappingFunc(result);
      ParseSuccess(u, remaining)
  }

  opaque function Not<R>(underlying: Parser<R>): Parser<()>
    // Returns a parser that succeeds if the underlying parser fails
    // and vice-versa. The result does not consume any input
  {
    (input: Input) =>
      var l := underlying(input);
      if l.IsFailure() then
        if l.IsFatal() then l.PropagateFailure()
        else ParseSuccess((), input)
      else ParseFailure(Recoverable, FailureData("not failed", input, Option.None))
  }

  opaque function And<L, R>(
    left: Parser<L>,
    right: Parser<R>
  ) : (p: Parser<(L, R)>)
    // Make the two parsers parse the same string and, if both suceed,
    // returns a pair of the two results, with the remaining of the right
  {
    (input: Input) =>
      var (l, remainingLeft) :- left(input);
      var (r, remainingRight) :- right(input);
      ParseSuccess((l, r), remainingRight)
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
    (input: Input) =>
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
    if |alternatives| == 0 then FailWith("no alternatives") else
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
    (input: Input) =>
      var p := underlying(input);
      if p.IsFailure() then
        if p.IsFatal() then
          p
        else
          p.(data := FailureData(p.data.message, input, Option.None))
      else
        p.(remaining := input)
  }

  /** `?(a)` evaluates `a` on the input, and then
      - If `a` succeeds, returns the result unchanged.
      - If `a` fails, and the failure is not fatal, propagate the same failure but without consuming input.
      `?(a)` is useful when there are other alternatives to parse and a parsed partially and we are ok with trying something else. */
  opaque function ?<R>(underlying: Parser<R>): (p: Parser<R>)
  {
    (input: Input) =>
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

  lemma AboutMaybe(input: Input)
    requires A.Length(input) > 0
  {
    reveal FailWith();
    var u := FailWith<char>("Error")(input);
    reveal Maybe();
    assert Maybe<char>(FailWith("Error"))(input)
        == ParseSuccess(Wrappers.None, input);
    var committedFailure := ParseFailure(Recoverable, FailureData("", A.Drop(input, 1), Option.None));
    reveal ResultWith();
    assert Maybe<char>(ResultWith(committedFailure))(input)
        == committedFailure.PropagateFailure();
  }

  /** `Maybe(a)` evaluates `a` on the input, and then
  - If `a` succeeds, then wraps its result with `Some(...)`
  - If `a` fails, and the failure is not fatal and did not consume input, succeeds with `None`.
    If the error is fatal or did consume input, fails with the same failure.*/
  opaque function Maybe<R>(underlying: Parser<R>): Parser<Option<R>>
  {
    (input: Input) =>
      var u := underlying(input);
      if u.IsFatalFailure() || (u.IsFailure() && !u.NeedsAlternative(input)) then u.PropagateFailure()
      else
      if u.ParseSuccess? then u.Map(result => Option.Some(result))
      else ParseSuccess(Option.None, input)
  }

  opaque function ConcatMap<L, R, T>(
    left: Parser<L>,
    right: Parser<R>,
    mapper: (L, R) -> T
  ) : (p: Parser<T>)
    // Apply two consecutive parsers consecutively
    // If both succeed, apply the mapper to the result and return it
  {
    (input: Input)
    =>
      var (l, remaining) :- left(input);
      var (r, remaining2) :- right(remaining);
      ParseSuccess(mapper(l, r), remaining2)
  }

  opaque function Concat<L, R>(
    left: Parser<L>,
    right: Parser<R>
  ) : (p: Parser<(L, R)>)
    // Apply two consecutive parsers consecutively
    // If both succeed, return the pair of the two results
  {
    (input: Input) =>
      var (l, remaining) :- left(input);
      var (r, remaining2) :- right(remaining);
      ParseSuccess((l, r), remaining2)
  }

  opaque function ConcatKeepRight<L, R>(
    left: Parser<L>,
    right: Parser<R>
  ) : (p: Parser<R>)
    // Return only the result of the right parser if the two parsers match
  {
    ConcatMap(left, right, (l, r) => r)
  }

  opaque function ConcatKeepLeft<L, R>(
    left: Parser<L>,
    right: Parser<R>
  ) : (p: Parser<L>)
    // Return only the result of the right parser if the two parsers match
  {
    ConcatMap(left, right, (l, r) => l)
  }

  /** Use a function that can print to debug, and possibly modify the parser*/
  opaque function Debug<R, D>(underlying: Parser<R>, name: string, onEnter: (string, Input) -> D, onExit: (string, D, ParseResult<R>) -> ()): (p: Parser<R>) {
    (input: Input) =>
      var debugData := onEnter(name, input);
      var output := underlying(input);
      var _ := onExit(name, debugData, output);
      output
  }

  // A datatype that avoid a quadratic complexity in concatenating long sequences.

  datatype SeqB<A> = SeqBCons(last: A, init: SeqB<A>) | SeqBNil {
    function Append(elem: A): SeqB<A> {
      SeqBCons(elem, this)
    }
    function Length(): nat {
      if SeqBNil? then 0 else 1 + init.Length()
    }
    function ToSequence(): seq<A>
      ensures |ToSequence()| == Length()
    {
      if SeqBNil? then [] else init.ToSequence() + [last]
    } by method {
      if SeqBNil? {
        return [];
      }
      var defaultElem := last;
      var l := Length();
      var elements := new A[l](i => defaultElem);
      var t := this;
      var i := l;
      assert t.ToSequence() + elements[i..] == ToSequence();
      while !t.SeqBNil?
        decreases i
        invariant 0 <= i <= l
        invariant i == t.Length()
        invariant t.ToSequence() + elements[i..] == ToSequence()
      {
        i := i - 1;
        elements[i] := t.last;
        t := t.init;
        assert t.ToSequence() + elements[i..] == ToSequence();
      }
      return elements[..];
    }
  }

  opaque function ZeroOrMore<R>(
    underlying: Parser<R>
  ): Parser<seq<R>>
    // Repeats the underlying parser until the first failure
    // that accepts alternatives, and returns the underlying sequence
  {
    Map(Rep(underlying, (result: SeqB<R>, r: R) => result.Append(r), SeqBNil),
        (result: SeqB<R>) => result.ToSequence())
  }

  opaque function OneOrMore<R>(underlying: Parser<R>): (p: Parser<seq<R>>)
    // Repeats the underlying parser until the first failure
    // Will return a failure if there is not at least one match
  {
    Bind(underlying, (r: R) =>
           Map(
             Rep(underlying, (result: SeqB<R>, r: R) => result.Append(r), SeqBCons(r, SeqBNil)),
             (result: SeqB<R>) => result.ToSequence()
           ))
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
    (input: Input) => Rep_(underlying, combine, acc, input)
  }

  opaque function RepSep<A, B>(
    underlying: Parser<A>,
    separator: Parser<B>
  ): Parser<seq<A>>
    // Repeats the underlying parser interleaved with a separator
    // Returns a sequence of results
  {
    Bind(
      Maybe(underlying),
      (result: Option<A>) =>
        if result.None? then SucceedWith<seq<A>>([]) else
        Map(
          Rep(
            ConcatKeepRight(separator, underlying),
            (acc: SeqB<A>, a: A) => acc.Append(a),
            SeqBCons(result.value, SeqBNil)),
          (result: SeqB<A>) => result.ToSequence()))
  }

  opaque function RepMerge<A>(
    underlying: Parser<A>,
    merger: (A, A) -> A
  ): Parser<A>
    // Repeats the underlying parser interleaved with a separator
    // Returns a sequence of results
  {
    Bind(Maybe(underlying), (result: Option<A>) =>
           if result.None? then FailWith<A>("No first element in RepMerge", Recoverable) else
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
           if result.None? then FailWith<A>("No first element in RepSepMerge", Recoverable) else
           Rep(ConcatKeepRight(separator, underlying), (acc: A, a: A) => merger(acc, a), result.value))
  }

  opaque function {:tailrecursion true} Rep_<A, B>(
    underlying: Parser<B>,
    combine: (A, B) -> A,
    acc: A,
    input: Input
  ): (p: ParseResult<A>)
    decreases A.Length(input)
    // ZeroOrMore the underlying parser over the input until a recoverable failure happens
    // and returns the accumulated results
  {
    match underlying(input)
    case ParseSuccess(result, remaining) =>
      if A.Length(remaining) >= A.Length(input) then ParseSuccess(acc, input) else
      Rep_(underlying, combine, combine(acc, result), remaining)
    case failure =>
      if failure.NeedsAlternative(input) then
        ParseSuccess(acc, input)
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
    (input: Input) => Recursive_(underlying, input)
  }

  function RecursiveProgressError<R>(name: string, input: A.Input, remaining: Input): (r: ParseResult<R>)
    requires A.Length(input) <= A.Length(remaining)
    ensures r.IsFailure()
  {
    if A.Length(remaining) == A.Length(input) then
      ParseFailure(Recoverable, FailureData(name + " no progress in recursive parser", remaining, Option.None))
    else
      ParseFailure(Fatal, FailureData(name + "fixpoint called with an increasing remaining sequence", remaining, Option.None))
  }

  opaque function Recursive_<R(!new)>(
    underlying: Parser<R> -> Parser<R>,
    input: Input
  ): (p: ParseResult<R>)
    // Implementation for Recursive()
    decreases A.Length(input)
  {
    var callback: Parser<R> :=
      (remaining: Input) =>
        if A.Length(remaining) < A.Length(input) then
          Recursive_(underlying, remaining)
        else
          RecursiveProgressError<R>("Parsers.Recursive", input, remaining);
    underlying(callback)(input)
  }

  /** Same as Recursive() but will not consume stack */
  function RecursiveNoStack<R>(underlying: Parser<RecursiveNoStackResult<R>>): Parser<R> {
    (input: Input) =>
      RecursiveNoStack_(underlying, underlying, input, [])
  }


  /** Datatype to store continuation for stack-free recursive parser */
  datatype RecursiveNoStackResult<!R> =
    | RecursiveReturn(R)
    | RecursiveContinue(R -> Parser<RecursiveNoStackResult<R>>)

  // Private implementation detail to make it tail-recursive
  type RecursiveCallback<!R> = Parser<RecursiveNoStackResult<R>>

  /** Tail-recursive auxiliary function for RecursiveNoStack() */
  @IsolateAssertions
  function RecursiveNoStack_<R>(
    continuation: Parser<RecursiveNoStackResult<R>>,
    underlying: Parser<RecursiveNoStackResult<R>>,
    input: Input,
    callbacks: seq<ParseResult<R> -> RecursiveCallback<R>>
  )
    : (result: ParseResult<R>)
    decreases A.Length(input), |callbacks|
  {
    var (recursor, remaining) :- continuation(input);
    match recursor
    case RecursiveReturn(result) =>
      if |callbacks| == 0 then
        ParseSuccess(result, remaining)
      else
        var toCompute := callbacks[0](ParseSuccess(result, remaining));
        if A.Length(input) < A.Length(remaining) then
          // This is a validity error: parsers should never consume less than zero
          RecursiveProgressError<R>("Parsers.RecursiveNoStack[internal]", input, remaining)
        else
          RecursiveNoStack_<R>(toCompute, underlying, remaining, callbacks[1..])
    case RecursiveContinue(rToNewParserOfRecursiveNoStackResultOfR) =>
      if A.Length(input) <= A.Length(remaining)  then
        RecursiveProgressError<R>("Parsers.RecursiveNoStack", input, remaining)
      else
        RecursiveNoStack_<R>(underlying, underlying, remaining,
                             [
                               (p: ParseResult<R>) =>
                                 if p.IsFailure() then
                                   ResultWith(p.PropagateFailure())
                                 else
                                   var (r, remaining2) := p.Extract();
                                   rToNewParserOfRecursiveNoStackResultOfR(r)
                             ]
                             + callbacks)
  }

  opaque function RecursiveMap<R(!new)>(
    underlying: map<string, RecursiveDef<R>>,
    fun: string): (p: Parser<R>)
    // Given a map of name := recursive definitions,
    // provide the result of this parser to the recursive definitions
    // and set 'fun' as the initial parser.
    // Careful: This function is not tail-recursive and will consume stack
  {
    (input: Input) => RecursiveMap_(underlying, fun, input)
  }

  datatype RecursiveDef<!R> = RecursiveDef(
    order: nat,
    definition: ParserSelector<R> -> Parser<R>
  ) // The order must be decreasing every time the function steps in
  // But it can jump to a bigger order if the input is consumed

  opaque function RecursiveMap_<R(!new)>(
    underlying: map<string, RecursiveDef<R>>,
    fun: string,
    input: Input
  ): (p: ParseResult<R>)
    // Implementation for RecursiveMap()
    decreases A.Length(input), if fun in underlying then underlying[fun].order else 0
  {
    if fun !in underlying then ParseFailure(Fatal, FailureData("parser '"+fun+"' not found", input, Option.None)) else
    var RecursiveDef(orderFun, definitionFun) := underlying[fun];
    var callback: ParserSelector<R>
      :=
      (fun': string) =>
        (var p : Parser<R> :=
           if fun' !in underlying.Keys then
             FailWith(fun' + " not defined", Fatal)
           else
             var RecursiveDef(orderFun', definitionFun') := underlying[fun'];
             (remaining: Input) =>
               if A.Length(remaining) < A.Length(input) || (A.Length(remaining) == A.Length(input) && orderFun' < orderFun) then
                 RecursiveMap_(underlying, fun', remaining)
               else if A.Length(remaining) == A.Length(input) then
                 ParseFailure(Recoverable, FailureData("non-progressing recursive call requires that order of '"
                                                       +fun'+"' ("+Strings.OfInt(orderFun')+") is lower than the order of '"+fun+"' ("+Strings.OfInt(orderFun)+")", remaining, Option.None))
               else
                 ParseFailure(Fatal, FailureData("parser did not return a suffix of the input", remaining, Option.None))
           ; p);
    definitionFun(callback)(input)
  }

  opaque function CharTest(test: C -> bool, name: string): (p: Parser<C>)
    // A parser that returns the current char if it passes the test
    // Returns a recoverable error based on the name otherwise
  {
    (input: Input) =>
      if 0 < A.Length(input) && test(A.CharAt(input, 0)) then ParseSuccess(A.CharAt(input, 0), A.Drop(input, 1))
      else ParseFailure(Recoverable,
                        FailureData("expected a "+name, input, Option.None))
  }

  opaque function DigitToInt(c: char): int {
    match c
    case '0' => 0 case '1' => 1 case '2' => 2 case '3' => 3 case '4' => 4
    case '5' => 5 case '6' => 6 case '7' => 7 case '8' => 8 case '9' => 9
    case _ => -1
  }

  opaque function StringToInt(s: string): int
    // Converts a string to a string
    decreases |s|
  {
    if |s| == 0 then 0 else
    if |s| == 1 then DigitToInt(s[0])
    else if s[0] == '-' then
      0 - StringToInt(s[1..])
    else
      StringToInt(s[0..|s|-1])*10 + StringToInt(s[|s|-1..|s|])
  }
}