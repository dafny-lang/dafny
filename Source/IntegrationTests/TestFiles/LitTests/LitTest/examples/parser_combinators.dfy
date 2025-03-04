/// # Parser combinators in Dafny
///
/// *Clément Pit-Claudel*, 2022-09-27
///
/// Challenge: define parse combinators.  As a usability test, use them to parse
/// expressions of the form `(ⁿ)ⁿ` (`n` opening parentheses followed by `n`
/// closing parentheses).
///
/// For a refresher on parser combinators, you may find the following tutorials useful:
///
/// - An Introduction To Scala Parser Combinators - Part 1: Parser Basics
///   https://henkelmann.eu/2011/01/an-introduction-to-scala-parser-combinators---part-1-parser-basics/
///
/// - Using Parsec (from _Real World Haskell_)
///   http://book.realworldhaskell.org/read/using-parsec.html
///
/// This challenge is tricky because we can't write what we'd usually write in
/// Haskell or OCaml:
///
/// ```ocaml
/// let parentheses' () =
///   (either
///      (concat (char '(') (concat (fun () -> parentheses' ()) (char ')')))
///      epsilon)
/// let parentheses () =
///   (concat parentheses' eos)
/// ```
///
/// Dafny rejects this definition because it cannot prove that the
/// `parentheses'` function terminates.  This is because Dafny analyses
/// anonymous functions (“lambdas”) modularly: every time a lambda is created,
/// as with `(fun () -> parentheses' ())`, Dafny checks that the function can be
/// called in any context.  To see why, consider the function `Apply` below and
/// the following two uses of it (see also parser_combinators_error.dfy):

function Apply(f: () -> int): int { f() }

// function F0(): int { Apply(F0) } // cannot use F0 naked here (see parser_combinators_error.dfy)
function F1(): int { Apply(() => F1()) }

/// Dafny rejects `F0` because it does not allow using “naked” recursive
/// functions, so one must wrap it in an anonymous function, as done in `F1
/// (this is called “eta-expanding”, or “thunking”).  Dafny also rejects `F1`,
/// however, because it is not always safe to call (in OCaml, it would loop
/// forever).
///
/// The `parentheses'` parser above *is* always safe to call, but Dafny doesn't
/// know that, so we need to do a bit more work to *prove* that it does.
///
/// We do it by using stronger specifications to enforce progress, as
/// shown in the solution below:

module {:options "-functionSyntax:4"} Parsers {

/// (The `-functionSyntax:4` enables Dafny's new function syntax, where
/// `function` replaces `function method`)
///
/// ## Utility types
///
/// `Either<L, R>` represents the result of the `Either` combinator.  For `And`,
/// we just use built-in pairs.

  datatype Either<+L, +R> = Left(l: L) | Right(r: R)

/// The result of a parse is either a failure that doesn't move the cursor, or a
/// success that moves the cursor.  An alternative encoding would record the
/// `delta` by which an operation moved the cursor, rather than its new position
/// (the verification works the same way).
///
/// Concretely, we define a `ParseResult` datatype with two cases, `Failure` and
/// `Success` (for simplicity, `Failure` does not record error locations).

  datatype ParseResult<+T> = Failure | Success(pos: nat, t: T) {

/// Then, we augment `ParseResult` that turn it into a “failure-compatible” type
/// (https://dafny.org/dafny/DafnyRef/DafnyRef#sec-failure-compatible-types),
/// i.e. one that can be used with the monadic `:-` operator.  This makes
/// error handling much less intrusive.

    predicate IsFailure() { Failure? }
    function PropagateFailure<U>(): ParseResult<U> requires Failure? { Failure() }
    function Extract(): (nat, T) requires Success? { (pos, t) }
    function MapResult<T'>(f: T -> T'): ParseResult<T'> {
      match this
        case Success(pos, t) => Success(pos, f(t))
        case Failure() => Failure()
    }
  }

/// We can then define combinators as functions that produce `ParseResult`s.  A
/// combinator is a partial function from a position (an index into the input
/// string) to a parse result.  Using partial functions allows us to prove
/// termination: for example, we may state that a recursive call to a parser may
/// only happen with an index larger than the current one.

  type Parser<+T> = nat --> ParseResult<T>

/// The following is a convenient trick when defining many functions that share
/// an argument without having to pass that argument everywhere and without
/// having to specify that all calls use the same value of that argument: we
/// define an `Engine` to be a datatype that contains an `input` string, and
/// members of the datatype can access it through the implicit `this` pointer
/// (of course, they don't have to: some members below are `static`).  This is
/// similar to using a `class` or `trait` to hold together related pieces of
/// information and to define functions on them.

  datatype Engine = Engine(input: string) {

/// `Concat` takes two parsers and creates a new one: a lambda (captured in the
/// type `Parser<(L, R)>`) that returns a pair of values, or `Failure`.  Because
/// the input parsers are partial functions, so it their combination: the
/// `requires` clauses on the lambda specify that the left parser may be called
/// (`left.requires(pos)`) and that the right parser may be called, but only if
/// the left one succeeds, and only on the position returned by it.

    static function Concat0<L, R>(left: Parser<L>, right: Parser<R>)
      : (p: Parser<(L, R)>)
    {
      (pos: nat)
        requires left.requires(pos)
        requires left(pos).Success? ==> right.requires(left(pos).pos)
      =>
        var (pos, l) :- left(pos);
        var (pos, r) :- right(pos);
        Success(pos, (l, r))
    }

/// The definition above is transparent: every time the verifier encounters it,
/// it is allowed to peek inside the body of the function and use it for
/// reasoning.  This will cause verification-performance issues down the line,
/// so we use the following alternative definition instead:

    static function {:opaque} Concat<L, R>(
      left: Parser<L>,
      right: Parser<R>
    )
      : (p: Parser<(L, R)>)
      ensures forall pos: nat |
        && left.requires(pos)
        && (left(pos).Success? ==> right.requires(left(pos).pos))
        :: p.requires(pos)
    {
      (pos: nat)
        requires left.requires(pos)
        requires left(pos).Success? ==> right.requires(left(pos).pos)
      =>
        var (pos, l) :- left(pos);
        var (pos, r) :- right(pos);
        Success(pos, (l, r))
    }

/// The two important things to note are (1) the fact that `Concat` is now
/// marked `:opaque`, and (2) the fact that `Concat` now has an `ensures` clause
/// of the following form:
///
/// ```dafny
///   ensures forall input :: (precondition of the parser) ==> p.requires(input)
/// ```
///
/// This does not say that the parser must accept all inputs: only that the
/// condition `(precondition of the parser)` is sufficient to call the opaque
/// function `p` that `Concat` return. (For clarity, a real implementation would
/// likely define a predicate to avoid repeating the precondition.)
///
/// With that in mind, we can define `Either` in the same way:

    static function {:opaque} Either<L, R>(
      left: Parser<L>,
      right: Parser<R>
    )
      : (p: Parser<Either<L, R>>)
      ensures forall pos: nat |
        && left.requires(pos)
        && (left(pos).Failure? ==> right.requires(pos))
        :: p.requires(pos)
    {
      (pos: nat)
        requires left.requires(pos)
        requires left(pos).Failure? ==> right.requires(pos)
      =>
        match left(pos)
          case Failure => right(pos).MapResult(r => Right(r))
          case Success(pos, l) => Success(pos, Left(l))
    }

/// Next, we define `Char`, which checks for a specific character and advances
/// the cursor by one.  Its post-condition indicates that the cursor has
/// advanced.  It additionally states that the new position is `<= |input|`
/// (which is equivalent to saying that the original position was `< |input|`).

    function {:opaque} Char(c: char): (p: Parser<char>)
      ensures forall pos: nat :: p.requires(pos)
      ensures forall pos: nat :: p(pos).Success? ==>
        p(pos).pos == pos + 1 && p(pos).pos <= |input|
    {
      (pos: nat) =>
        if pos < |input| && input[pos] == c then Success(pos + 1, c)
        else Failure()
    }

/// Finally, `EOS` (“End Of String”) checks whether all input has been consumed…

    const EOS: Parser<()> :=
      (pos: nat) => if pos >= |input| then Success(pos, ()) else Failure()

/// … and `Epsilon` matches the empty string:

    static const Epsilon: Parser<()> :=
      (pos: nat) => Success(pos, ())

/// These combinators are enough to define a parser for parentheses.  Note that
/// because the parser calls itself, we need to eta-expand it (so that we can
/// mention `pos` in its spec).  Also note the call to `MapResult`, which
/// implements a simple semantic action (here, counting parentheses).

    function {:opaque} Parentheses'(pos: nat): ParseResult<nat>
      decreases |input| - pos
    {
      var rec := pos' requires pos < pos' <= |input| => Parentheses'(pos');
      Either(Concat(Char('('), Concat(rec, Char(')'))), Epsilon)(pos)
        .MapResult<nat>(
          var count := (r: Either<(char, (nat, char)), ()>) =>
            match r
              case Left((c, (n, c'))) => n + 1
              case Right(()) => 0;
          count
        )
    }

/// 0. We would like to call `Either(…)` with position `pos`.  For that, we need
///    to prove its `requires`:
///
///    0. The first `requires` of the lambda returned by `Either` is
///       `left.requires(…)`, where `left` is `Concat(Char('('), …))`:
///
///       0. The first `requires` of the lambda returned by `Concat` is
///          `left.requires(…)`, where `left` is `Char('(')`.  But `Char` returns a
///          `lambda` with no preconditions, so there is nothing to prove here.
///
///       1. The second `requires` of that lambda states that we can call `right`
///          with the position returned by `left` (i.e. by `Char(…)`).  Here `right`
///          is `Concat(rec, Char(')'))`, and postcondition of `Char` tells us that
///          this position (let's call it `pos'`) is the previous position plus one,
///          and that `pos'` is `<= |input|`.
///
///          0. The first `requires` on `Concat(rec, …)` states that we can call
///             `rec` with position `pos'`, which is `pos + 1`.  The precondition of
///             `rec` is `pos < pos' <= |input|` (as written in the source code),
///             and is satisfied given the postcondition of `Char`.
///
///          1. The second `requires` on `Concat(rec, …)` is the fact that we can
///             call `Char`, which is always true.
///
///    1. The second requires of the outermost call to `Either` states that we can
///       call `Epsilon` if the left parser fails.  `Epsilon` can always be called,
///       so this succeeds trivially as well.
///
/// The crucial point here is that, by combining the pre and post-conditions of all
/// of the parsers, we are able to symbolically propagate the fact that the parser
/// makes progress between one call to `Parentheses'` and the next, and hence that
/// the recursion is safe.
///
/// Phew!  Now all that is left is to check for the end of the string:

    function Parentheses(pos: nat): ParseResult<nat> {
      Concat(Parentheses', EOS)(pos)
        .MapResult<nat>((r: (nat, ())) => r.0)
    }
  }

/// The resulting parser is easy to call.  Here is a small driver to test it,
/// which you can invoke by passing input strings as command line arguments:
///
/// ```
/// $ Dafny -compile:4 parser_combinators.dfy --args "" "((()))" "((()))no" "((())"
///
/// Dafny program verifier finished with 8 verified, 0 errors
/// "": 0 nested parentheses
/// "((()))": 3 nested parentheses
/// "((()))no": no valid parse
/// "((())": no valid parse
/// ```

  method Main(args: seq<string>) {
    if |args| <= 1 {
      return;
    }
    for i := 1 to |args| {
      var input := args[i];
      print "\"", input, "\"", ": ";
      match Engine(input).Parentheses(0) {
        case Success(_, n) => print n, " nested parentheses";
        case Failure() => print "no valid parse";
      }
      print "\n";
    }
  }
}

/// ## Exercises
///
/// Here is a nice exercise that requires a bit of refactoring:
///
/// ### `Map` combinator
///
/// Wrap parsers into a datatype, and define a member function that takes
/// applies a semantic action directly on the parser, rather than having to
/// apply the parser and using `MapResult`.  Something like below, but making it
/// a member function will work much better with type inference:
///
/// ```dafny
/// function {:opaque} Map<T, T'>(p: Parser<T>, f: T -> T'): (p': Parser<T'>)
///   ensures forall pos: nat :: p.requires(pos) ==> p'.requires(pos)
/// {
///   (pos: nat) requires p.requires(pos) => p(pos).MapResult<T'>(f)
/// }
/// ```

// NONUNIFORM: testDafnyForEachCompiler does not support program argument
// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %run --no-verify "%s" "((()))" "((()))no" "((())" >> "%t"
// RUN: %diff "%s.expect" "%t"
