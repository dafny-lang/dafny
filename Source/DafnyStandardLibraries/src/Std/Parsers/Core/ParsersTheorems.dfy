/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

abstract module Std.Parsers.Theorems refines Core {
  import opened Collections.Tuple

  ghost predicate Trigger<T>(i: T) { true }

  opaque ghost predicate NeverFatal<R>(underlying: Parser<R>)
    // A parser is NeverFatal iff for any input, it never returns a fatal error
    // Since fatal errors occur only when a parser returns more characters than it was given,
    // NeverFatal means the remaining unparsed must be smaller or equal to the input
  {
    forall input: Input | Trigger(input) :: // Otherwise the trigger underlying(input) is not working well
      && (underlying(input).ParseFailure? ==> underlying(input).level == Recoverable)
      && IsRemaining(input, underlying(input).Remaining())
  }

  lemma AboutSucceedWith<R>(result: R, input: Input)
    ensures
      var p := SucceedWith(result);
      && p(input).ParseSuccess?
      && p(input).remaining == input
  { reveal SucceedWith(); }

  lemma AboutFail<R>(message: string, level: FailureLevel, input: Input)
    ensures
      var p := FailWith<R>(message, level)(input);
      && p.ParseFailure?
      && p.data == FailureData(message, input, Option.None)
      && p.level == level
  {
    reveal FailWith();
  }

  lemma AboutFail_2<R>(message: string, input: Input)
    ensures
      var p := FailWith<R>(message)(input);
      && p.ParseFailure?
      && p.level == Recoverable
      && p.data == FailureData(message, input, Option.None)
  {
    reveal FailWith();
  }

  lemma AboutBind_<L, R>(
    left: Parser<L>,
    right: (L, Input) -> Parser<R>,
    input: Input
  )
    ensures
      var p := BindSucceeds(left, right)(input);
      && var leftResult := left(input);
      && !leftResult.IsFailure()
      ==> var leftValues := left(input).Extract();
          && var rightResult := right(leftValues.0, leftValues.1)(leftValues.1);
          && !rightResult.IsFailure()
          ==> && !p.IsFailure()
              && p.remaining == rightResult.remaining
              && p.result == rightResult.result
  {
    reveal BindSucceeds();
  }

  lemma AboutMap_<R, U>(underlying: Parser<R>, mappingFunc: R -> U, input: Input)
    ensures var p := Map(underlying, mappingFunc);
            && (underlying(input).ParseSuccess? <==> p(input).ParseSuccess?)
            && (p(input).ParseSuccess? ==>
                  && p(input).remaining == underlying(input).remaining
                  && p(input).result == mappingFunc(underlying(input).result))
  {
    reveal Map();
    reveal BindSucceeds();
    reveal SucceedWith();
  }

  function BindMapCallback<R, U>(mappingFunc: R -> U):
    (R, Input) -> Parser<U>
  {
    (result: R, remaining: Input) => SucceedWith(mappingFunc(result))
  }

  lemma AboutMap_Bind_<R, U>(underlying: Parser<R>, mappingFunc: R -> U, input: Input)
    ensures Map(underlying, mappingFunc)(input)
         == BindSucceeds<R, U>(underlying, BindMapCallback(mappingFunc))(input)
  {
    reveal Map();
    reveal BindSucceeds();
    reveal SucceedWith();
  }

  lemma AboutConcat<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: Input)
    ensures var p := Concat(left, right);
            && (p(input).ParseSuccess? ==>
                  && left(input).ParseSuccess?
                  && p(input).result.0 == left(input).result
                  && var input2 := left(input).remaining;
                  && right(input2).ParseSuccess?
                  && p(input).result.1 == right(input2).result
                  && p(input).remaining == right(input2).remaining)
  {
    reveal Concat();
    reveal ConcatMap();
  }

  function BindConcatCallback<L, R>(right: Parser<R>): (L, Input) -> Parser<(L, R)>
  {
    (l: L, remaining: Input) =>
      Map(right, (r: R) => (l, r))
  }

  lemma AboutConcatBindSucceeds<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: Input)
    ensures Concat(left, right)(input) == BindSucceeds(left, BindConcatCallback(right))(input)
  {
    reveal Concat();
    reveal BindSucceeds();
    reveal SucceedWith();
    reveal Map();
    reveal ConcatMap();
  }

  lemma AboutConcatKeepRight<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: Input)
    ensures var p := ConcatKeepRight(left, right);
            && (p(input).ParseSuccess? ==>
                  && left(input).ParseSuccess?
                  && var input2 := left(input).remaining;
                  && right(input2).ParseSuccess?
                  && p(input).result == right(input2).result
                  && p(input).remaining == right(input2).remaining)
  {
    reveal ConcatKeepRight();
    reveal ConcatMap();
  }

  lemma AboutConcatConcatKeepRight<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: Input)
    ensures Map(Concat(left, right), T2_1())(input) == ConcatKeepRight(left, right)(input)
  {
    reveal Concat();
    reveal SucceedWith();
    reveal ConcatKeepRight();
    reveal Map();
    reveal ConcatMap();
  }


  lemma AboutConcatKeepLeft<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: Input)
    ensures var p := ConcatKeepLeft(left, right);
            && (p(input).ParseSuccess? ==>
                  && left(input).ParseSuccess?
                  && var input2 := left(input).remaining;
                  && right(input2).ParseSuccess?
                  && p(input).result == left(input).result
                  && p(input).remaining == right(input2).remaining)
  {
    reveal ConcatKeepLeft();
    reveal ConcatMap();
  }
  lemma AboutConcatConcatKeepLeft<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: Input)
    ensures Map(Concat(left, right), T2_0())(input) == ConcatKeepLeft(left, right)(input)
  {
    reveal Concat();
    reveal SucceedWith();
    reveal ConcatKeepLeft();
    reveal Map();
    reveal ConcatMap();
  }

  predicate AboutRepIncreasesPosIfUnderlyingSucceedsAtLeastOnce_Ensures<R>(
    underlying: Parser<R>,
    acc: seq<R>,
    input: Input
  )
  {
    var result := ZeroOrMore(underlying)(input);
    && result.ParseSuccess?
    && |acc| <= |result.result|
    && (underlying(input).ParseSuccess? && A.Length(underlying(input).remaining) < A.Length(input)
        ==>
          (|acc| < |result.result| && A.Length(result.remaining) < A.Length(input)))
  }

  predicate AboutFix_Ensures<R(!new)>(
    underlying: Parser<R> -> Parser<R>,
    input: Input)
  {
    var p := Recursive_(underlying, input);
    p.ParseSuccess? ==> IsRemaining(input, p.remaining)
  }

  opaque function CallUnderlyingCallbackInput<R(!new)>(underlying: Parser<R> -> Parser<R>, callback: Parser<R>, input: Input): ParseResult<R> {
    underlying(callback)(input)
  }

  opaque predicate IsRemainingFix<R(!new)>(underlying: Parser<R> -> Parser<R>, callback: Parser<R>, input: Input) {
    IsRemaining(input, CallUnderlyingCallbackInput(underlying, callback, input).Remaining())
  }

  @IsolateAssertions
  lemma AboutFix<R(!new)>(
    underlying: Parser<R> -> Parser<R>,
    input: Input)
    requires
      forall callback: Parser<R>, u: Input
        | CallUnderlyingCallbackInput(underlying, callback, u).ParseSuccess?
        :: IsRemainingFix(underlying, callback, input)
    ensures AboutFix_Ensures(underlying, input)
  {
    reveal Recursive_();
    hide IsRemaining();
    var p := Recursive_(underlying, input);
    if p.ParseSuccess? {
      var callback: Parser<R> :=
        (remaining: Input) =>
          if A.Length(remaining) < A.Length(input) then
            Recursive_(underlying, remaining)
          else
            RecursiveProgressError<R>("Parsers.Recursive", input, remaining);
      assert p == underlying(callback)(input);

      assert forall c: Parser<R>, u: Input
          |    CallUnderlyingCallbackInput(underlying, c,        u).ParseSuccess?
          :: IsRemainingFix(underlying, c,        input);
      InstantiateForallManually(underlying, callback, input);
      assert CallUnderlyingCallbackInput(underlying, callback, input).ParseSuccess? by {
        reveal CallUnderlyingCallbackInput();
      }
      assert IsRemainingFix(underlying, callback, input);
      assert IsRemaining(input, underlying(callback)(input).Remaining()) by {
        reveal IsRemainingFix();
        reveal CallUnderlyingCallbackInput();
      }
      assert IsRemaining(input, p.remaining);
    }
  }
  lemma InstantiateForallManually<R(!new)>(
    underlying: Parser<R> -> Parser<R>,
    callback: Parser<R>,
    input: Input)
    requires forall c: Parser<R>, u: Input
               |    CallUnderlyingCallbackInput(underlying, c,        u).ParseSuccess?
               :: IsRemainingFix(underlying, c,        input)
    ensures CallUnderlyingCallbackInput(underlying, callback, input).ParseSuccess? ==>
              IsRemainingFix(   underlying, callback, input)
  {
  }


  predicate AboutRecursiveMap_Ensures<R(!new)>(
    underlying: map<string, RecursiveDef<R>>,
    fun: string,
    input: Input
  ) {
    var p := RecursiveMap_(underlying, fun, input);
    && (p.ParseSuccess? ==> IsRemaining(input, p.remaining))
  }


  lemma SucceedWithValid<R>(result: R)
    ensures NeverFatal(SucceedWith(result))
  { reveal NeverFatal(), SucceedWith();
  }

  lemma SucceedWithValidAuto<R>()
    ensures forall result: R :: NeverFatal(SucceedWith(result))
  { reveal NeverFatal(), SucceedWith();  }

  lemma EpsilonValid()
    ensures NeverFatal(Epsilon())
  { reveal NeverFatal(), Epsilon(); SucceedWithValid(()); }

  lemma AboutEpsilon(input: Input)
    ensures
      var p := Epsilon();
      && p(input).ParseSuccess?
      && p(input).remaining == input
  {
    reveal Epsilon();
    reveal SucceedWith();
  }

  lemma FailValid<R>(message: string)
    ensures NeverFatal<R>(FailWith(message, Recoverable))
  { reveal FailWith(); reveal NeverFatal(); }

  lemma FailValidAuto<R>()
    ensures forall message :: NeverFatal<R>(FailWith(message, Recoverable))
  { reveal FailWith(); reveal NeverFatal(); }

  ghost predicate BindRightValid<L(!new), R>(right: (L, Input) -> Parser<R>) {
    forall l: L, input: Input :: NeverFatal(right(l, input))
  }

  @IsolateAssertions @ResourceLimit("5e5")
  lemma BindSucceedsValid<L(!new), R>(
    left: Parser<L>,
    right: (L, Input) -> Parser<R>
  )
    requires NeverFatal(left)
    requires BindRightValid(right)
    ensures NeverFatal(BindSucceeds(left, right))
  {
    reveal BindSucceeds(), NeverFatal();
    var p := BindSucceeds(left, right);
    forall input: Input | Trigger(input) ensures
        && (p(input).ParseFailure? ==> p(input).level == Recoverable)
        && IsRemaining(input, p(input).Remaining())
    {
      var pResult := left(input);
      if pResult.ParseSuccess? {
        var (leftResult, remaining) := pResult.Extract();
        var _ := Trigger(remaining);
        var r := right(leftResult, remaining);
        assert NeverFatal(r);
        assert IsRemaining(input, remaining);
        assert IsRemaining(remaining, r(remaining).Remaining());
        assert p(input).Remaining() == r(remaining).Remaining();
        IsRemainingTransitive(input, remaining, p(input).Remaining());
        assert IsRemaining(input, p(input).Remaining());
      } else {
        assert IsRemaining(input, p(input).Remaining());
      }
      assert IsRemaining(input, p(input).Remaining());
    }
    assert NeverFatal(p);
  }

  ghost predicate BindValidRight<L(!new), R(!new)>(left: Parser<L>)
    requires NeverFatal(left)
  {
    forall right: (L, Input) -> Parser<R> | BindRightValid(right) ::
      NeverFatal(BindSucceeds(left, right))
  }

  lemma BindValidAuto<L(!new), R(!new)>()
    ensures forall left: Parser<L> | NeverFatal(left) ::
              BindValidRight<L, R>(left)
  {
    forall left: Parser<L> | NeverFatal(left),
      right: (L, Input) -> Parser<R> | BindRightValid(right)
      ensures
        NeverFatal(BindSucceeds(left, right))
    {
      BindSucceedsValid(left, right);
    }
  }
}
