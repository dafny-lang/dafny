/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

// A domain-specific language (DSL) for building parsers that uses minimal syntax
// (including single-letter combinators like M or C) to visually separate the parser logic
// (constants, strings, and custom parser calls) from the underlying combinator
// machinery. This makes complex parser definitions more readable by reducing
// syntactic noise.
abstract module Std.Parsers.Builders {
  import P: Core
  export
    provides P
    provides O
    provides SucceedWith
    provides FailWith
    provides ResultWith
    provides Rec
    provides MId
    provides B.Apply
    provides B.e_I
    provides B.I_e
    provides B.I_I
    provides B.M, B.M2, B.M3
    provides B.If
    provides B.?
    provides B.??
    provides B.Then
    provides B.ThenWithRemaining
    provides B.Bind
    provides B.Rep
    provides B.RepFold
    provides B.RepSep
    provides B.RepMerge
    provides B.RepSepMerge
    provides B.Rep1
    provides B.Debug
    provides B.End
    provides EOS
    provides Nothing
    provides CharTest
    provides ToInput
    provides RecNoStack
    provides RecursiveProgressError
    // Verbose
    provides MapIdentity
    provides B.Option
    provides B.FailureResetsInput
    provides B.ConcatKeepRight
    provides B.ConcatKeepLeft
    provides B.Concat
    provides B.Map
    provides B.Map2
    provides B.Map3
    provides EndOfString
    provides Or
    provides B.Repeat
    provides B.RepeatFold
    provides B.RepeatSeparator
    provides B.RepeatMerge
    provides B.RepeatSeparatorMerge
    provides B.RepeatAtLeastOnce
    provides Recursive
    provides RecursiveNoStack
    provides RecursiveMap

    reveals NonProgressing
    reveals Input
    reveals InputLength
    reveals C
    reveals ParseResult
    reveals B
    reveals Rec, RecMap
    reveals RecMapDef, FailureLevel, RecMapSel
    reveals RecNoStackResult

  type Input = P.Input
  type C = P.C

  /** `FailureLevel` is an alias for `P.FailureLevel`. Recoverable or Fatal */
  type FailureLevel = P.FailureLevel
  /** A mapping from string to a parser returning `A` */
  type RecMapSel<A> = string -> B<A>
  /** `ParseResult` is an alias for `P.ParseResult`. */
  type ParseResult<+T> = P.ParseResult<T>

  function ToInput(other: seq<C>): (i: Input)

  /** `SucceedWith(a)` returns success on any input,
      `.value` contains the provided value.*/
  function SucceedWith<T>(t: T): B<T> {
    B(P.SucceedWith(t))
  }

  /** `FailWith(message)` returns a failure on any input, and does not consume input. */
  function FailWith<T>(message: string, level: FailureLevel := P.Recoverable): B<T> {
    B(P.FailWith(message,  level))
  }

  /** A parser that always returns the given result  */
  function ResultWith<R>(result: ParseResult<R>): B<R>
  {
    B(P.ResultWith(result))
  }

  /** Parses nothing, always returns a success with nothing consumed. Can be useful in alternatives. */
  const Nothing: B<()> := B(P.Epsilon())

  /** An identity function useful for B.M2 and B.M3 . Short version of MapIdentity() */
  function MId<R>(r: R): R { r }

  /** An identity function useful for B.Map2 and B.Map3 . Can be abbreviated into MId() */
  function MapIdentity<R>(r: R): R { r }

  /** Adapter to wrap any underlying parser so that they can be chained together. */
  datatype B<R> = B(apply: P.Parser<R>)
  {
    function Apply(input: seq<C>): ParseResult<R> {
      apply(ToInput(input))
    }

    /** `a.?()` evaluates `a` on the input, and then  
        - If `a` succeeds, then wraps its result with `Some(...)`  
        - If `a` fails, and the failure is not fatal and did not consume input, succeeds with `None`.  
          If the error is fatal or did consume input, fails with the same failure.
        Verbose equivalent: `a.Option()`
      */
    function ?(): B<P.Option<R>> {
      B(P.Maybe(apply))
    }

    /** Verbose equivalent of `a.?()` */
    function Option(): B<P.Option<R>> {
      B(P.Maybe(apply))
    }

    /** `a.??()` evaluates `a` on the input, and then  
        - If `a` succeeds, returns the result unchanged.  
        - If `a` fails, and the failure is not fatal, propagate the same failure but without consuming input.  
         `a.??()` is useful when there are other alternatives to parse and a parsed partially and we are ok with trying something else.
        Verbose equivalent: `a.FailureResetsInput()`   
      */
    function ??(): B<R> {
      B(P.?(apply))
    }

    /** `a.FailureResetsInput()` is the verbose equivalent of `a.??()` */
    function FailureResetsInput(): B<R> {
      B(P.?(apply))
    }

    /** `a.e_I(b)` (exclude include) evaluates `a` on the input, and then  
        - If `a` succeeds, executes `b` on what `a` left behind and returns that result, ignoring `a`.  
        - If `a` fails, returns that failure instead.  
        See also `I_e` (include exclude)
        You can chain the calls e.g.

            a.e_I(b).e_I(c)
            a.e_I(b.e_I(c))  
        
        will parse a, b, c but only return the result of `c`.
        Verbose equivalent: `a.ConcatKeepRight(b)` */
    function e_I<U>(other: B<U>): (p: B<U>)
    {
      B(P.ConcatKeepRight(apply, other.apply))
    }

    /** `a.ConcatKeepRight(b)` is the verbose equivalent of `a.e_I(b)` */
    function ConcatKeepRight<U>(other: B<U>): (p: B<U>)
    {
      e_I(other)
    }

    /** `a.I_e(b)` (include exclude) evaluates `a` on the input, and then  
        - If `a` succeeds, executes `b` on what `a` left behind.  
          - If `b` succeeds, returns what `a` parsed along with what `b` left behind.  
        - If `a` fails, returns that failure.  
        See also `e_I` (exclude include). You can chain the calls e.g.

            a.I_e(b).I_e(c)
            a.I_e((b.I_e(c))
        
        will parse a, b, c but only return the result of `a`.
        Verbose equivalent: `a.ConcatKeepLeft(b)`.  */
    function I_e<U>(other: B<U>): (p: B<R>)
    {
      B(P.ConcatKeepLeft(apply, other.apply))
    }

    /** `a.ConcatKeepLeft(b)` is the verbose equivalent of `a.I_e(b)` */
    function ConcatKeepLeft<U>(other: B<U>): (p: B<R>)
    {
      I_e(other)
    }

    /** `a.I_I(b)` (include include) evaluates `a` on the input, and then  
        - If `a` succeeds, executes `b` on what `a` left behind.  
          - If `b` succeeds, returns a pair of what `a` and `b` resulted with along with what `b` left behind.  
        - If `a` or `b` fail, returns that failure.  
        See also `e_I` and `I_e`
        You can chain the calls e.g.

            a.I_I(b).I_I(c)
        
        will parse a, b, c and return the result of `((a, b), c)`.
        Verbose equivalent: `a.Concat(b)`. */
    function I_I<U>(other: B<U>): (p: B<(R, U)>)
    {
      B(P.Concat(apply, other.apply))
    }

    /** `a.Concat(b)` is the verbose equivalent of `a.I_I(b)` */
    function Concat<U>(other: B<U>): (p: B<(R, U)>)
    {
      I_I(other)
    }

    /** `a.If(cond)` evaluates `cond` on the input, and then:
        If cond returns a success, evaluates `a` on the original string and returns the result of `a`.
        If cond evaluates to a failure, returns the same failure.
        
        For example, `a.If(b.??())` is a way to test the parser b as a lookahead without committing anything.
         */
    function If<U>(cond: B<U>): (p: B<R>) {
      B(P.If(cond.apply, apply))
    }

    /** `a.M(f)` evaluates `a` on the input, and then if it returns a success,  
        transforms the value using the function `f`.
        Verbose equivalent: `a.Map(f)`. */
    function M<U>(mappingFunc: R -> U): (p: B<U>) {
      B(P.Map(apply, mappingFunc))
    }

    /** `a.Map(f)` is the verbose equivalent of `a.M(f)`. */
    function Map<U>(mappingFunc: R -> U): (p: B<U>) {
      M(mappingFunc)
    }

    /** `a.M2(unfolder, f)` evaluates `a` on the input, and then transforms its result to a pair
        thanks to unfolder, on which it can apply the mapping function. Short version of `.Map2()`.
        If the parser returns a pair already, use `Mid()` as built-in unfolder.
        Verboe equivalent: `a.Map2(unfolder, f)` */
    function M2<R1, R2, U>(unfolder: R -> (R1, R2), mappingFunc: (R1, R2) -> U): (p: B<U>) {
      B(P.Map(apply, (x: R) => var x := unfolder(x); mappingFunc(x.0, x.1)))
    }

    /** `a.Map2(unfolder, f)` is the verbose equivalent of `a.M2(unfolder, f)`.
        If the parser returns a triplet already, use `MapIdentity()` as built-in unfolder. */
    function Map2<R1, R2, U>(unfolder: R -> (R1, R2), mappingFunc: (R1, R2) -> U): (p: B<U>) {
      M2(unfolder, mappingFunc)
    }

    /** `a.M3(unfolder, f)` evaluates `a` on the input, and then extracts its result to a triplet
        thanks to unfolder, on which it can apply the mapping function.
        Verbose equivalent: `a.Map3(unfolder, f)`.
        If the parser returns a triplet already, use `MId()` as built-in unfolder. */
    function M3<R1, R2, R3, U>(unfolder: R -> (R1, R2, R3), mappingFunc: (R1, R2, R3) -> U): (p: B<U>) {
      B(P.Map(apply, (x: R) => var x := unfolder(x); mappingFunc(x.0, x.1, x.2)))
    }

    /** `a.Map3(unfolder, f)` is the verbose equivalent of `a.M3(unfolder, f)`. */
    function Map3<R1, R2, R3, U>(unfolder: R -> (R1, R2, R3), mappingFunc: (R1, R2, R3) -> U): (p: B<U>) {
      M3(unfolder, mappingFunc)
    }

    /** `a.Then(f)` evaluates `a` on the input, and if it is a success,  
         computes the parser f(result) and executes it on the remaining that `a` did not parse.  
         The return value is what f(result) returns.  
         If `a` returns a failure, returns that failure.
         If `f` is a constant parser b, it is the same as `a.e_I(b)` */
    function Then<V>(other: R -> B<V>): (p: B<V>)
    {
      B(P.Bind(apply, (result: R) => other(result).apply))
    }

    /** `a.ThenWithRemaining(f)` evaluates `a` on the input, and if it is a success,  
         computes the parser f(result, remainingInput) and executes it on the remaining that `a` did not parse.  
         The return value is what f(result) returns.  
         If `a` returns a failure, returns that failure.
         If `f` is a constant parser b, it is the same as `a.e_I(b)` */
    function ThenWithRemaining<V>(other: (R, Input) -> B<V>): (p: B<V>)
    {
      B(P.BindSucceeds(apply,  (result: R, input: Input) => other(result, input).apply))
    }

    /** `a.Bind(f)` evaluates `a` on the input.
         Then it computes the parser f(parse result, original input) and executes it on the remaining that `a` did not parse.  
         The return value is what f(result) returns.
         To only bind in case of success, see `a.ThenWithRemaining(_)` or simply `a.Then(_)` */
    function Bind<V>(other: (ParseResult<R>, Input) -> B<V>): (p: B<V>)
    {
      B(P.BindResult(apply, (result: ParseResult<R>, input: Input) => other(result, input).apply))
    }

    /** `a.Debug(name, onEnter, onExit)` first calls `onEnter(name, input)` when it is executed, obtains the data `d: D`  
         then it calls `a` on the input (that's the result)
         then it calls `onExit(name, d, result)`
         then it return the result.
         Very useful for debugging, see the README on how to use it. Typically `D` is the input itself. */
    function Debug<D>(name: string, onEnter: (string, Input) -> D, onExit: (string, D, ParseResult<R>) -> ()): B<R> {
      B(P.Debug(apply, name, onEnter, onExit))
    }

    /** `a.RepFold(init, combine)` will consider init as an accumulator, and every time `a` succeeds and parses some input, it will
        combine(init, result) for the new accumulator value.  
        If `a` fails once while consuming input, it returns the failure.
        Verbose equivalent: `a.RepeatFold(init, combine)`.
        */
    function RepFold<A>(init: A, combine: (A, R) -> A): (p: B<A>)
    {
      B(P.Rep(apply, combine, init))
    }

    /** `a.RepeatFold(init, combine)` is the verbose equivalent of `a.RepFold(init, combine)`. */
    function RepeatFold<A>(init: A, combine: (A, R) -> A): (p: B<A>)
    {
      RepFold(init, combine)
    }

    /** `a.RepSep(separator)` returns a sequence of `a` separated by the given separator parser. If the separator parser fails but consumed some input,
        returns that failure, you might have to suffix your separator with `.??()` if it is a complex separator.
        `a.RepSep(separator)` is equivalent to
        `a.?().Then(result => if result.None? then Succeed([]) else
          separator.e_I(a).Rep([result.a], (acc, newA) => acc + [newA])
        )`
        but it's optimized to avoid concatenation of a big sequence with a small one.
        Verbose equivalent: `a.RepeatSeparator(separator)`.
        
        See `.ZeroOrMore()` if you don't need a separator. */
    function RepSep<K>(separator: B<K>): (p: B<seq<R>>)
    {
      B(P.RepSep(apply, separator.apply))
    }

    /** `a.RepeatSeparator(separator)` is the verbose equivalent of `a.RepSep(separator)`  */
    function RepeatSeparator<K>(separator: B<K>): (p: B<seq<R>>)
    {
      RepSep(separator)
    }

    /** `a.RepMerge(merger)` parses `a` as long as possible and applies the merger on the previous result and the new output.
      * If `a` cannot be parsed the first time, does not consume any input and returns a recoverable failure.
      * Verbose equivalent: `a.RepeatMerge(merger)`
      */
    function RepMerge(merger: (R, R) -> R): (p: B<R>)
    {
      B(P.RepMerge(apply, merger))
    }

    /** `a.RepMerge(merger)` is the verbose equivalent of `.RepMerge()`. */
    function RepeatMerge(merger: (R, R) -> R): (p: B<R>)
    {
      RepMerge(merger)
    }

    /** `a.RepSepMerge(merger)` parses `a` as long as possible and applies the merger on the previous result and the new output,
      * parsing a potential separator in between.
      * If `a` cannot be parsed the first time, does not consume any input and returns a recoverable failure.
      * Verbose equivalent: `a.RepeatSeparatorMerge(merger)` */
    function RepSepMerge<K>(separator: B<K>, merger: (R, R) -> R): (p: B<R>)
    {
      B(P.RepSepMerge(apply, separator.apply, merger))
    }

    /** `a.RepeatSeparatorMerge(merger)` is the verbose equivalent of `a.RepSepMerge(merger)` */
    function RepeatSeparatorMerge<K>(separator: B<K>, merger: (R, R) -> R): (p: B<R>)
    {
      RepSepMerge(separator, merger)
    }

    /** `a.Rep()` keeps parsing `a` as long as the parser consumes some input. It returns a sequence of the parse results.
      * If returns a failure only if `a` returns a failure that partially parsed the input, or in case of a fatal error.
      * Verbose equivalent: `a.Repeat()`. */
    function Rep(): (p: B<seq<R>>)
    {
      B(P.ZeroOrMore(apply))
    }

    /** `a.Repeat()` is the verbose equivalent of `a.Rep()`. */
    function Repeat(): (p: B<seq<R>>)
    {
      Rep()
    }

    /** `a.Rep1()` keeps parsing `a` as long as the parser consumes some input. It returns a sequence of the parse results.
      * If returns a failure only if `a` does not parse at the beginning (even if it did not consume any input), or `a` returns a failure that partially parsed the input, or in case of a fatal error.
      * Verbose equivalent: `a.RepeatAtLeastOnce()`
      */
    function Rep1(): (p: B<seq<R>>)
    {
      B(P.OneOrMore(apply))
    }

    /** `a.RepeatAtLeastOnce()` is the verbose equivalent of  `a.Rep1()` */
    function RepeatAtLeastOnce(): (p: B<seq<R>>)
    {
      Rep1()
    }

    /** `a.End()` uses the parser `a` with the assertion that there is no input remaining afterwards, otherwise it fails with a recoverable error.
      * It's like a.I_e(EOS) */
    function End(): (p: B<R>)
    {
      this.I_e(EOS)
    }
  }

  /** `O([a, b, ...])` parses `a` on the input, and if `a` succeeds, returns its result.
      If `a` fails with a fatal error, returns the fatal error.
      If `a` fails and consumed some input, returns that error.
      If `a` fails but did not consume any input, continues parsing `b` and so on.
      If none of the alternatives parse the input, builds a more complex failure message indicating what each sub-parser was expecting.
      Verbose equivalent: `Or([a, b, ...])`
  */
  function O<R>(alternatives: seq<B<R>>): B<R>
    // Declares a set of alternatives as a single list
  {
    if |alternatives| == 0 then FailWith("no alternative") else
    if |alternatives| == 1 then alternatives[0]
    else
      B(P.Or(alternatives[0].apply, O(alternatives[1..]).apply))
  }

  /** `Or([a, b, ...])` is the verbose equivalent of `O([a, b, ...])`. */
  function Or<R>(alternatives: seq<B<R>>): B<R>
  {
    O(alternatives)
  }

  /** `EOS` succeeds only on an empty string (i.e. the end of the input). */
  const EOS: B<()> := B(P.EndOfString())


  /** `EndOfString` is the verbose equivalent of `EOS` */
  const EndOfString: B<()> := EOS

  /** `CharTest(test, name)` tests if the next char of the input satisfies the test, and if so, succeeds with the character.
      On failure, returns an error message like "expected a {name}" */
  function CharTest(test: C -> bool, name: string): B<C>
  {
    B(P.CharTest(test, name))
  }

  /** `Rec(a) takes a function that, given a parser, returns a parser.  
      It provides itself to this function so that makes it possible to create recursive parsers.  
      For example, to parse nested parentheses like () (()) ... (((((()))))) ..., you can do this:
      
          Rec(rec =>
            O([ 
              S("(").e_I(rec).I_e(S(")")).M(r => ()),
              Nothing
            ]))

      If on recursion, it detect that no input was consumed, it will raise a fatal error. Therefore, the following parser
      will return a fatal error on any input

          Rec(rec => rec)
      
      and it will explain

          Error: no progress in recursive parser
    
    Verbose equivalent: Recursive(underlying)
  */
  opaque function Rec<R(!new)>(
    underlying: B<R> -> B<R>
  ): B<R>
  {
    B(P.Recursive(
        (p: P.Parser<R>) =>
          underlying(B(p)).apply))
  }

  /** `Recursive(underlying)` is the verbose equivalent of `Rec(underlying)` */
  opaque function Recursive<R(!new)>(
    underlying: B<R> -> B<R>
  ): B<R>
  {
    Rec(underlying)
  }

  function InputLength(input: Input): nat {
    P.A.Length(input)
  }

  /** Returns true if there was no progress from input1 to input2 */
  predicate NonProgressing(input1: Input, input2: Input) {
    InputLength(input1) <= InputLength(input2)
  }

  /** Returns a meaningful error if there was no progress from input1 to input2 */
  function RecursiveProgressError<R>(name: string, input1: Input, input2: Input): P.ParseResult<R>
    requires NonProgressing(input1, input2)
  {
    P.RecursiveProgressError(name, input1, input2)
  }

  // Conversion to/from RecursiveNoStackResult requires proving an impossible termination
  datatype RecNoStackResult<!R> =
    | RecReturn(toReturn: R)
      // Immediatley return an R
    | RecContinue(toContinue: (R, Input) -> B<RecNoStackResult<R>>)
  // Ask to parse an R recursively, and then continue with the given parser.
  // It is possible to chain RecContinue.

  // Private implementation detail to make it tail-recursive
  type RecCallback<!R> = B<RecNoStackResult<R>>

  /**
    * RecNoStack is a specialized recursive parser builder that avoids stack overflow
    * by using an explicit continuation-passing style approach.
    *
    * Parameters:
    * - underlying: B<RecNoStackResult<R>> - A parser builder that returns a RecNoStackResult,
    *   which consists of either
    *    | RecReturn(R)
    *    | RecContinue(R -> Parser<RecNoStackResult<R>>)
    *
    * Returns:
    * - B<R> - A parser builder that will eventually produce a result of type R
    */
  opaque function RecNoStack<R(!new)>(
    underlying: B<RecNoStackResult<R>>
  ): B<R>
  {
    B((input: Input) => RecNoStack_(underlying, underlying, input, input, []))
  }

  /** `RecursiveNoStack(underlying)` is the verbose equivalent of `RecNoStack(underlying)` */
  function RecursiveNoStack<R(!new)>(
    underlying: B<RecNoStackResult<R>>
  ): B<R>
  {
    RecNoStack(underlying)
  }

  /** Tail-recursive auxiliary function for RecursiveNoStack() */
  function RecNoStack_<R>(
    continuation: B<RecNoStackResult<R>>,
    underlying: B<RecNoStackResult<R>>,
    input: P.Input,
    previousInput: P.Input,
    callbacks: seq<ParseResult<R> -> RecCallback<R>>
  )
    : (result: ParseResult<R>)
    decreases P.A.Length(input), P.A.Length(previousInput), |callbacks|
  {
    var continuationResult := continuation.apply(input);
    var remaining := continuationResult.Remaining();
    if continuationResult.IsFailure() || continuationResult.Extract().0.RecReturn? then
      var parseResult :=
        if continuationResult.IsFailure() then
          continuationResult.PropagateFailure()
        else
          P.ParseSuccess(continuationResult.Extract().0.toReturn, remaining);
      if |callbacks| == 0 then
        parseResult
      else
        var toCompute := callbacks[0](parseResult);
        if P.A.Length(input) < P.A.Length(remaining) then
          // This is a validity error: parsers should never consume less than zero
          RecursiveProgressError<R>("Parsers.RecNoStack[internal]", input, remaining)
        else if P.A.Length(previousInput) < P.A.Length(input) then
          RecursiveProgressError<R>("Parsers.RecNoStack[internal]", previousInput, input)
        else
          // Because callbacks decreases, it's ok to not consume input there
          RecNoStack_<R>(toCompute, underlying, remaining, input, callbacks[1..])
    else
      var recursor := continuationResult.Extract().0;
      assert recursor.RecContinue?;
      var rToNewParserOfRecursiveNoStackResultOfR := recursor.toContinue;
      if P.A.Length(remaining) < P.A.Length(input)  then
        RecNoStack_<R>(
          underlying, underlying, remaining, remaining,
          [ (p: ParseResult<R>) =>
              if p.IsFailure() then
                B(P.ResultWith(p.PropagateFailure()))
              else
                var (r, remaining2) := p.Extract();
                rToNewParserOfRecursiveNoStackResultOfR(r, remaining2)]
          + callbacks)
      else if P.A.Length(remaining) == P.A.Length(input) &&
              P.A.Length(remaining) < P.A.Length(previousInput) then
        RecNoStack_<R>(
          underlying, underlying, remaining, remaining,
          [ (p: ParseResult<R>) =>
              if p.IsFailure() then
                B(P.ResultWith(p.PropagateFailure()))
              else
                var (r, remaining2) := p.Extract();
                rToNewParserOfRecursiveNoStackResultOfR(r, remaining2)]
          + callbacks)
      else
        RecursiveProgressError<R>("ParserBuilders.RecNoStack", input, remaining)
  }

  /** Datatype used for the values of underlying in `RecMap(underlying, fun)`, see below */
  datatype RecMapDef<!R> = RecMapDef(
    order: nat,
    definition: RecMapSel<R> -> B<R>)

  /** `RecMap(underlying, fun) is a generalization of Rec().
      underlying is a map from function names to definitions that
        - Contain a natural order number
        - Contain a function that accepts a parser and return a parser.
      The parameter `fun` determines which definition is called first.
      If a function (e.g. mul) calls a parser (e.g. add) with a greater order number and the same input,
      it will fail with an error message like

          non-progressing recursive call requires that order of 'add' (3) is lower than the order of 'mul' (2)
      
      This guarantees the termination of all parsers.
      For example, to parse any well-formed expression with parentheses like (), (()(()())), you can do this:
      
          RecMap(
            map[
              "parens" := RecMapDef(0, rec =>
                S("(").e_I(rec("list")).I_e(S(")")).M(r => ())
              ),
              "list" := RecMapDef(1, rec => O([ 
                  rec("parens")).I_I(rec("list")).M(r => ())
                  Epsilon
                ]))
              )
            ],
            "list")
      
      if you try to call into a function that does not exist, it will fail at the time of parsing with a fatal error.
      If on recursion to a higher order, it detects that no input was consumed, it will raise a fatal error similar to Rec().
      This construct can be extremely useful for parsing arithmetic expressions.
  */
  opaque function RecMap<R(!new)>(
    underlying: map<string, RecMapDef<R>>,
    startFun: string): (p: B<R>)
  {
    B(P.RecursiveMap(
        map k <- underlying ::
          k :=
          P.RecursiveDef(
            underlying[k].order,
            (selector: P.ParserSelector<R>) =>
              underlying[k].definition(
                (name: string) =>
                  B(selector(name))
              ).apply),
        startFun
      ))
  }

  /** `RecursiveMap(underlying, startFun)` is the verbose equivalent of `RecMap(underlying, startFun)` */
  opaque function RecursiveMap<R(!new)>(
    underlying: map<string, RecMapDef<R>>,
    startFun: string): (p: B<R>)
  {
    RecMap(underlying, startFun)
  }
}
