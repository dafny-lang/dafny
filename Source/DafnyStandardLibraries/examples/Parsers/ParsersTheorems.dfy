abstract module Std.Parsers.ExampleParsersTheorems refines Core {

  ghost predicate Trigger<T>(i: T) { true }

  opaque ghost predicate Valid<R>(underlying: Parser<R>)
    // A parser is valid iff for any input, it never returns a fatal error
    // and always returns a suffix of its input
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

  lemma AboutFail_<R>(message: string, level: FailureLevel, input: Input)
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

  lemma AboutConcatR<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: Input)
    ensures var p := ConcatR(left, right);
            && (p(input).ParseSuccess? ==>
                  && left(input).ParseSuccess?
                  && var input2 := left(input).remaining;
                  && right(input2).ParseSuccess?
                  && p(input).result == right(input2).result
                  && p(input).remaining == right(input2).remaining)
  {
    reveal ConcatR();
    reveal ConcatMap();
  }

  function first<L, R>(): ((L, R)) -> L {
    (lr: (L, R)) => lr.0
  }
  function second<L, R>(): ((L, R)) -> R {
    (lr: (L, R)) => lr.1
  }
  lemma AboutConcatConcatR<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: Input)
    ensures Map(Concat(left, right), second())(input) == ConcatR(left, right)(input)
  {
    reveal Concat();
    reveal SucceedWith();
    reveal ConcatR();
    reveal Map();
    reveal ConcatMap();
  }


  lemma AboutConcatL<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: Input)
    ensures var p := ConcatL(left, right);
            && (p(input).ParseSuccess? ==>
                  && left(input).ParseSuccess?
                  && var input2 := left(input).remaining;
                  && right(input2).ParseSuccess?
                  && p(input).result == left(input).result
                  && p(input).remaining == right(input2).remaining)
  {
    reveal ConcatL();
    reveal ConcatMap();
  }
  lemma AboutConcatConcatL<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: Input)
    ensures Map(Concat(left, right), first())(input) == ConcatL(left, right)(input)
  {
    reveal Concat();
    reveal SucceedWith();
    reveal ConcatL();
    reveal Map();
    reveal ConcatMap();
  }

  predicate AboutRepIncreasesPosIfUnderlyingSucceedsAtLeastOnceEnsures<R>(
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

  lemma {:vcs_split_on_every_assert} AboutFix<R(!new)>(
    underlying: Parser<R> -> Parser<R>,
    input: Input)
    requires
      forall callback: Parser<R>, u: Input
        | underlying(callback)(u).ParseSuccess?
        :: IsRemaining(input, underlying(callback)(input).Remaining())
    ensures AboutFix_Ensures(underlying, input)
  {
    reveal Recursive_();
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
    ensures Valid(SucceedWith(result))
  { reveal Valid(), SucceedWith();
  }

  lemma SucceedWithValidAuto<R>()
    ensures forall result: R :: Valid(SucceedWith(result))
  { reveal Valid(), SucceedWith();  }

  lemma EpsilonValid()
    ensures Valid(Epsilon())
  { reveal Valid(), Epsilon(); SucceedWithValid(()); }

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
    ensures Valid<R>(FailWith(message, Recoverable))
  { reveal FailWith(); reveal Valid(); }

  lemma FailValidAuto<R>()
    ensures forall message :: Valid<R>(FailWith(message, Recoverable))
  { reveal FailWith(); reveal Valid(); }

  ghost predicate BindRightValid<L(!new), R>(right: (L, Input) -> Parser<R>) {
    forall l: L, input: Input :: Valid(right(l, input))
  }

  @IsolateAssertions @ResourceLimit("5e5")
  lemma BindSucceedsValid<L(!new), R>(
    left: Parser<L>,
    right: (L, Input) -> Parser<R>
  )
    requires Valid(left)
    requires BindRightValid(right)
    ensures Valid(BindSucceeds(left, right))
  {
    reveal BindSucceeds(), Valid();
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
        assert Valid(r);
        assert IsRemaining(input, remaining);
        assert IsRemaining(remaining, r(remaining).Remaining());
        assert p(input).Remaining() == r(remaining).Remaining();
        IsRemainingTransitive(input, remaining, p(input).Remaining());
        assert IsRemaining(input, p(input).Remaining());
      } else {
        assert IsRemaining(input, p(input).Remaining());
      }
      assert IsRemaining(input, p(input).Remaining());
      //reveal v;
    }
    assert Valid(p);
  }

  ghost predicate BindValidRight<L(!new), R(!new)>(left: Parser<L>)
    requires Valid(left)
  {
    forall right: (L, Input) -> Parser<R> | BindRightValid(right) ::
      Valid(BindSucceeds(left, right))
  }

  lemma BindValidAuto<L(!new), R(!new)>()
    ensures forall left: Parser<L> | Valid(left) ::
              BindValidRight<L, R>(left)
  {
    forall left: Parser<L> | Valid(left),
      right: (L, Input) -> Parser<R> | BindRightValid(right)
      ensures
        Valid(BindSucceeds(left, right))
    {
      BindSucceedsValid(left, right);
    }
  }

  lemma IntToStringThenStringToIntIdem(n: int)
    decreases if n < 0 then 1 - n else n
    ensures 0 <= n ==> 1 <= |IntToString(n)| && IntToString(n)[0] != '-'
    ensures StringToInt(IntToString(n)) == n
  {
    reveal IntToString(), StringToInt(), DigitToInt();
    if n < 0 {
      calc {
        StringToInt(IntToString(n));
        StringToInt("-" + IntToString(-n));
        0 - StringToInt(IntToString(-n));
        { IntToStringThenStringToIntIdem(-n); }
        n;
      }
    } else if 0 <= n <= 9 {
      assert StringToInt(IntToString(n)) == n;
    } else {
      assert IntToString(n) == IntToString(n / 10) + IntToString(n % 10);
      var s := IntToString(n);
    }
  }
  opaque predicate IsStringInt(s: string): (b: bool)
    ensures b ==> |s| > 0
  {
    |s| > 0 &&
    if s[0] == '-' then
      |s| > 1 && s[1] != '0' &&
      (forall i | 1 <= i < |s| :: s[i] in "0123456789")
    else
      (|s| > 1 ==> s[0] != '0') &&
      (forall i | 0 <= i < |s| :: s[i] in "0123456789")
  }

  lemma StringToIntNonnegative(s: string)
    requires IsStringInt(s)
    requires s[0] != '-'
    decreases |s|
    ensures 0 <= StringToInt(s)
    ensures s != "0" ==> 0 < StringToInt(s)
    ensures |s| > 1 ==> 10 <= StringToInt(s)
  {
    if |s| == 0 {

    } else if |s| == 1 {
      reveal DigitToInt(), StringToInt(), IsStringInt();
      match s[0]
      case '0' => case '1' => case '2' => case '3' => case '4' =>
      case '5' => case '6' => case '7' => case '8' => case '9' =>
      case _ =>
    } else if s[0] == '-' {
    } else {
      assert !(|s|  == 0 || |s| == 1 || s[0] == '-');
      reveal StringToInt();
      assert StringToInt(s) == StringToInt(s[0..|s|-1])*10 + StringToInt(s[|s|-1..|s|]);
      assert IsStringInt(s[0..|s|-1]) by {
        reveal IsStringInt();
      }
      StringToIntNonnegative(s[..|s|-1]);
      var tail := s[|s|-1..|s|];
      assert IsStringInt(tail) && tail[0] != '-' by {
        reveal IsStringInt();
      }
      StringToIntNonnegative(tail);
      reveal IsStringInt();
      assert |s| > 1 ==> 10 <= StringToInt(s);
    }
  }

  @IsolateAssertions
  lemma StringToIntThenIntToStringIdem(s: string)
    requires IsStringInt(s)
    decreases |s|
    ensures s[0] != '-' ==> 0 <= StringToInt(s)
    ensures |s| == 1 ==> 0 <= StringToInt(s) <= 9
    ensures IntToString(StringToInt(s)) == s
  {
    assert |s| > 0;
    if 1 <= |s| && s[0] == '-' {
      reveal IntToString(), StringToInt(), IsStringInt();
      assert forall i | 1 <= i < |s| :: s[i] in "0123456789";
      calc {
        IntToString(StringToInt(s));
        IntToString(0 - StringToInt(s[1..]));
      }
    } else if |s| == 1 {
      reveal IntToString(), StringToInt(), IsStringInt(), DigitToInt();
      calc {
        IntToString(StringToInt(s));
        s;
      }
    } else {
      var n := StringToInt(s);
      StringToIntNonnegative(s);
      var init := s[..|s|-1];
      var last := s[|s|-1..|s|];
      var q := StringToInt(init);
      var r := StringToInt(last);
      assert IsStringInt(init) by { reveal IsStringInt(); }
      assert IsStringInt(last) by { reveal IsStringInt(); }
      StringToIntThenIntToStringIdem(init);
      StringToIntThenIntToStringIdem(last);
      assert StringToInt(s) ==
             StringToInt(s[0..|s|-1])*10 + StringToInt(s[|s|-1..|s|]) by {
        reveal StringToInt();
      }
      assert n == q * 10 + r;
      calc {
        IntToString(n);
        { reveal IntToString();
          assert !(n < 0);
          assert n != 0;
        }
        IntToString(n / 10) + IntToString(n % 10);
        s;
      }
    }
  }
}
