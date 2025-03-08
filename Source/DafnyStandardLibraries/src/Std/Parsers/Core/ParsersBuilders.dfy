// Nice wDSL to build parsers to avoid too much parenthesis nesting
// B(p)       returns a parser builder from a normal parser.
// B1.o_I(B2) will parse both but return the result of B2
// B1.I_o(B2) will parse both but return the result of B1
// B.M(f)     will map the result of the parser builder by f if succeeded
// B1.O(B2)   will either parse B1, or B2 if B1 fails with Recoverable
// FirstOf([B1, B2, B3])
//            will parse with B1, but if B1 fails with Recoverable,
//            it will parse with B2, but if B2 fails with Recoverable,
//            it will parse with B3
// R(v)       returns a parser builder that returns immediately v
// 
// There are more parser builders in the trait Engine, when their spec depends on
// a predetermined input, e.g. to tests for constant strings

abstract module Std.Parsers.Builders {
  import P: Core
  export
    provides P
    provides O
    provides SucceedWith
    provides FailWith
    provides Rec
    provides B.Apply
    provides B.e_I
    provides B.I_e
    provides B.I_I
    provides B.M
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
    provides IntToString
    provides CharTest
    provides ToInput
    reveals Input
    reveals C
    reveals ParseResult
    reveals B
    reveals Rec, RecMap
    reveals RecMapDef, FailureLevel, RecMapSel

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

  /** Parses nothing, always returns a success with nothing consumed. Can be useful in alternatives. */
  const Nothing: B<()> := B(P.Epsilon())

  /** Adapter to wrap any underlying parser so that they can be chained together. */
  datatype B<R> = B(apply: P.Parser<R>)
  {
    function Apply(input: seq<C>): ParseResult<R> {
      apply(ToInput(input))
    }

    /** `a.?()` evaluates `a` on the input, and then  
        - If `a` succeeds, then wraps its result with `Some(...)`  
        - If `a` fails, and the failure is not fatal and did not consume input, succeeds with `None`.  
          If the error is fatal or did consume input, fails with the same failure.*/
    function ?(): B<P.Option<R>> {
      B(P.Maybe(apply))
    }

    /** `a.??()` evaluates `a` on the input, and then  
        - If `a` succeeds, returns the result unchanged.  
        - If `a` fails, and the failure is not fatal, propagate the same failure but without consuming input.  
         `a.??()` is useful when there are other alternatives to parse and a parsed partially and we are ok with trying something else. */
    function ??(): B<R> {
      B(P.?(apply))
    }

    /** `a.e_I(b)` (exclude include) evaluates `a` on the input, and then  
        - If `a` succeeds, executes `b` on what `a` left behind and returns that result, ignoring `a`.  
        - If `a` fails, returns that failure instead.  
        See also `I_e` (include exclude)
        You can chain the calls e.g.

            a.e_I(b).e_I(c)
            a.e_I(b.e_I(c))  
        
        will parse a, b, c but only return the result of `c`. */
    function e_I<U>(other: B<U>): (p: B<U>)
    {
      B(P.ConcatR(apply, other.apply))
    }

    /** `a.I_e(b)` (include exclude) evaluates `a` on the input, and then  
        - If `a` succeeds, executes `b` on what `a` left behind.  
          - If `b` succeeds, returns what `a` parsed along with what `b` left behind.  
        - If `a` fails, returns that failure.  
        See also `e_I` (exclude include). You can chain the calls e.g.

            a.I_e(b).I_e(c)
            a.I_e((b.I_e(c))
        
        will parse a, b, c but only return the result of `a`. */
    function I_e<U>(other: B<U>): (p: B<R>)
    {
      B(P.ConcatL(apply, other.apply))
    }

    /** `a.I_I(b)` (include include) evaluates `a` on the input, and then  
        - If `a` succeeds, executes `b` on what `a` left behind.  
          - If `b` succeeds, returns a pair of what `a` and `b` resulted with along with what `b` left behind.  
        - If `a` or `b` fail, returns that failure.  
        See also `e_I` and `I_e`
        You can chain the calls e.g.

            a.I_I(b).I_I(c)
        
        will parse a, b, c and return the result of `((a, b), c)`. */
    function I_I<U>(other: B<U>): (p: B<(R, U)>)
    {
      B(P.Concat(apply, other.apply))
    }

    /** `a.If(cond)` evaluates `cond` on the input, and then if cond returns a success,  
        evalutes `a` on the original string and returns the result of `a`.  
        If cond evaluates to a failure, returns the same failure
        
        For example, a.If(b.??()) is a way to test the parser b as a lookahead without committing anything.
         */
    function If<U>(cond: B<U>): (p: B<R>) {
      B(P.If(cond.apply, apply))
    }

    /** `a.M(f)` evaluates `a` on the input, and then if it returns a success,  
        transforms the value using the function `f`. */
    function M<U>(mappingFunc: R -> U): (p: B<U>)
    {
      B(P.Map(apply, mappingFunc))
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

    /** `a.RepFold(init, combine) will consider init as an accumulator, and every time `a` succeeds and parses some input, it will
        combine(init, result) for the new accumulator value.  
        If `a` fails once while consuming input, it returns the failure. */
    function RepFold<A>(init: A, combine: (A, R) -> A): (p: B<A>)
    {
      B(P.Rep(apply, combine, init))
    }

    /** `a.RepSep(separator)` returns a sequence of `a` separated by the given separator parser. If the separator parser fails but consumed some input,
        returns that failure. You might have to suffix your separator with `.??()` if it is a complex separator.
        `a.RepSep(separator)` is equivalent to
        `a.?().Then(result => if result.None? then Succeed([]) else
          separator.e_I(a).Rep([result.a], (acc, newA) => acc + [newA])
        )`
        but it's optimized to avoid concatenation of a big sequence with a small one.
        
        See `.ZeroOrMore()` if you don't need a separator. */
    function RepSep<K>(separator: B<K>): (p: B<seq<R>>)
    {
      B(P.RepSep(apply, separator.apply))
    }

    /** `a.RepMerge(merger)` parses `a` as long as possible and applies the merger on the previous result and the new output.
      * If `a` cannot be parsed the first time, does not consume any input and returns a recoverable failure.
      */
    function RepMerge(merger: (R, R) -> R): (p: B<R>)
    {
      B(P.RepMerge(apply, merger))
    }

    /** `a.RepSepMerge(merger)` parses `a` as long as possible and applies the merger on the previous result and the new output,
      * parsing a potential separator in between.
      * If `a` cannot be parsed the first time, does not consume any input and returns a recoverable failure.
      */
    function RepSepMerge<K>(separator: B<K>, merger: (R, R) -> R): (p: B<R>)
    {
      B(P.RepSepMerge(apply, separator.apply, merger))
    }

    /** `a.Rep()` keeps parsing `a` as long as the parser consumes some input. It returns a sequence of the parse results.
      * If returns a failure only if `a` returns a failure that partially parsed the input, or in case of a fatal error. */
    function Rep(): (p: B<seq<R>>)
    {
      B(P.ZeroOrMore(apply))
    }

    /** `a.Rep1()` keeps parsing `a` as long as the parser consumes some input. It returns a sequence of the parse results.
      * If returns a failure only if `a` does not parse at the beginning (even if it did not consume any input), or `a` returns a failure that partially parsed the input, or in case of a fatal error. */
    function Rep1(): (p: B<seq<R>>)
    {
      B(P.OneOrMore(apply))
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
  */
  function O<R>(alternatives: seq<B<R>>): B<R>
    // Declares a set of alternatives as a single list
  {
    if |alternatives| == 0 then FailWith("no alternative") else
    if |alternatives| == 1 then alternatives[0]
    else
      B(P.Or(alternatives[0].apply, O(alternatives[1..]).apply))
  }

  /** `End` succeeds only on an empty string (i.e. the end of the input). */
  const EOS: B<()> := B(P.EndOfString())

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
  */
  opaque function Rec<R(!new)>(
    underlying: B<R> -> B<R>
  ): B<R>
  {
    B(P.Recursive((p: P.Parser<R>) =>
                    underlying(B(p)).apply))
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
    fun: string): (p: B<R>)
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
        fun
      ))
  }

  /** Provides a tool for converting an integer to a string */
  function IntToString(input: int): string {
    P.IntToString(input)
  }
}
