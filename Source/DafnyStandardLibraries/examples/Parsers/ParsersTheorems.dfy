abstract module ExampleParsersTheorems refines Std.Parsers.Core {
  lemma AboutSucceed<R>(result: R, input: seq<C>)
    ensures
      var p := Succeed(result);
      && p(input).Success?
      && p(input).remaining == input
  { reveal Succeed(); }

  lemma AboutFail_<R>(message: string, level: FailureLevel, input: seq<C>)
    ensures
      var p := Fail<R>(message, level)(input);
      && p.Failure?
      && p.data == FailureData(message, input, Option.None)
      && p.level == level
  {
    reveal Fail();
  }

  lemma AboutFail_2<R>(message: string, input: seq<C>)
    ensures
      var p := Fail<R>(message)(input);
      && p.Failure?
      && p.level == Recoverable
      && p.data == FailureData(message, input, Option.None)
  {
    reveal Fail();
  }

  lemma AboutBind_<L, R>(
    left: Parser<L>,
    right: (L, seq<C>) -> Parser<R>,
    input: seq<C>
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

  lemma AboutMap_<R, U>(underlying: Parser<R>, mappingFunc: R -> U, input: seq<C>)
    ensures var p := Map(underlying, mappingFunc);
            && (underlying(input).Success? <==> p(input).Success?)
            && (p(input).Success? ==>
                  && p(input).remaining == underlying(input).remaining
                  && p(input).result == mappingFunc(underlying(input).result))
  {
    reveal Map();
    reveal BindSucceeds();
    reveal Succeed();
  }

  function BindMapCallback<R, U>(mappingFunc: R -> U):
    (R, seq<C>) -> Parser<U>
  {
    (result: R, remaining: seq<C>) => Succeed(mappingFunc(result))
  }

  lemma AboutMap_Bind_<R, U>(underlying: Parser<R>, mappingFunc: R -> U, input: seq<C>)
    ensures Map(underlying, mappingFunc)(input)
         == BindSucceeds<R, U>(underlying, BindMapCallback(mappingFunc))(input)
  {
    reveal Map();
    reveal BindSucceeds();
    reveal Succeed();
  }

  lemma AboutConcat<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: seq<C>)
    ensures var p := Concat(left, right);
            && (p(input).Success? ==>
                  && left(input).Success?
                  && p(input).result.0 == left(input).result
                  && var input2 := left(input).remaining;
                  && right(input2).Success?
                  && p(input).result.1 == right(input2).result
                  && p(input).remaining == right(input2).remaining)
  {
    reveal Concat();
    reveal ConcatMap();
  }

  function BindConcatCallback<L, R>(right: Parser<R>): (L, seq<C>) -> Parser<(L, R)>
  {
    (l: L, remaining: seq<C>) =>
      Map(right, (r: R) => (l, r))
  }

  lemma AboutConcatBindSucceeds<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: seq<C>)
    ensures Concat(left, right)(input) == BindSucceeds(left, BindConcatCallback(right))(input)
  {
    reveal Concat();
    reveal BindSucceeds();
    reveal Succeed();
    reveal Map();
    reveal ConcatMap();
  }

  lemma AboutConcatR<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: seq<C>)
    ensures var p := ConcatR(left, right);
            && (p(input).Success? ==>
                  && left(input).Success?
                  && var input2 := left(input).remaining;
                  && right(input2).Success?
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
    input: seq<C>)
    ensures Map(Concat(left, right), second())(input) == ConcatR(left, right)(input)
  {
    reveal Concat();
    reveal Succeed();
    reveal ConcatR();
    reveal Map();
    reveal ConcatMap();
  }


  lemma AboutConcatL<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: seq<C>)
    ensures var p := ConcatL(left, right);
            && (p(input).Success? ==>
                  && left(input).Success?
                  && var input2 := left(input).remaining;
                  && right(input2).Success?
                  && p(input).result == left(input).result
                  && p(input).remaining == right(input2).remaining)
  {
    reveal ConcatL();
    reveal ConcatMap();
  }
  lemma AboutConcatConcatL<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: seq<C>)
    ensures Map(Concat(left, right), first())(input) == ConcatL(left, right)(input)
  {
    reveal Concat();
    reveal Succeed();
    reveal ConcatL();
    reveal Map();
    reveal ConcatMap();
  }

  predicate AboutRepIncreasesPosIfUnderlyingSucceedsAtLeastOnceEnsures<R>(
    underlying: Parser<R>,
    acc: seq<R>,
    input: seq<C>
  )
  {
    var result := ZeroOrMore(underlying)(input);
    && result.Success?
    && |acc| <= |result.result|
    && (underlying(input).Success? && |underlying(input).remaining| < |input|
        ==>
          (|acc| < |result.result| && |result.remaining| < |input|))
  }

  predicate AboutFix_Ensures<R(!new)>(
    underlying: Parser<R> -> Parser<R>,
    input: seq<C>)
  {
    var p := Recursive_(underlying, input);
    p.Success? ==> IsRemaining(input, p.remaining)
  }

  lemma {:vcs_split_on_every_assert} AboutFix<R(!new)>(
    underlying: Parser<R> -> Parser<R>,
    input: seq<C>)
    requires
      forall callback: Parser<R>, u: seq<C>
        | underlying(callback)(u).Success?
        :: IsRemaining(input, underlying(callback)(input).Remaining())
    ensures AboutFix_Ensures(underlying, input)
  {
    reveal Recursive_();
  }


  predicate AboutRecursiveMap_Ensures<R(!new)>(
    underlying: map<string, RecursiveDef<R>>,
    fun: string,
    input: seq<C>
  ) {
    var p := RecursiveMap_(underlying, fun, input);
    && (p.Success? ==> IsRemaining(input, p.remaining))
  }


  lemma SucceedValid<R>(result: R)
    ensures Valid(Succeed(result))
  { reveal Valid(), Succeed(); }

  lemma SucceedValidAuto<R>()
    ensures forall result: R :: Valid(Succeed(result))
  { reveal Valid(), Succeed();  }

  lemma EpsilonValid()
    ensures Valid(Epsilon())
  { reveal Valid(), Epsilon(); SucceedValid(()); }

  lemma AboutEpsilon(input: seq<C>)
    ensures
      var p := Epsilon();
      && p(input).Success?
      && p(input).remaining == input
  {
    reveal Epsilon();
    reveal Succeed();
  }

  lemma FailValid<R>(message: string)
    ensures Valid<R>(Fail(message, Recoverable))
  { reveal Fail(); reveal Valid(); }

  lemma FailValidAuto<R>()
    ensures forall message :: Valid<R>(Fail(message, Recoverable))
  { reveal Fail(); reveal Valid(); }

  ghost predicate BindRightValid<L(!new), R>(right: (L, seq<C>) -> Parser<R>) {
    forall l: L, input: seq<C> :: Valid(right(l, input))
  }

  lemma BindSucceedsValid<L(!new), R>(
    left: Parser<L>,
    right: (L, seq<C>) -> Parser<R>
  )
    requires Valid(left)
    requires BindRightValid(right)
    ensures Valid(BindSucceeds(left, right))
  {
    reveal BindSucceeds(), Valid();
    var p := BindSucceeds(left, right);
    forall input: seq<C> ensures
        && (p(input).Failure? ==> p(input).level == Recoverable)
        && IsRemaining(input, p(input).Remaining())
    {

    }
  }

  ghost predicate BindValidRight<L(!new), R(!new)>(left: Parser<L>)
    requires Valid(left)
  {
    forall right: (L, seq<C>) -> Parser<R> | BindRightValid(right) ::
      Valid(BindSucceeds(left, right))
  }

  lemma BindValidAuto<L(!new), R(!new)>()
    ensures forall left: Parser<L> | Valid(left) ::
              BindValidRight<L, R>(left)
  {
    forall left: Parser<L> | Valid(left),
      right: (L, seq<C>) -> Parser<R> | BindRightValid(right)
      ensures
        Valid(BindSucceeds(left, right))
    {
      BindSucceedsValid(left, right);
    }
  }

  lemma intToStringThenStringToIntIdem(n: int)
    decreases if n < 0 then 1 - n else n
    ensures 0 <= n ==> 1 <= |intToString(n)| && intToString(n)[0] != '-'
    ensures stringToInt(intToString(n)) == n
  {
    reveal intToString(), stringToInt(), digitToInt();
    if n < 0 {
      calc {
        stringToInt(intToString(n));
        stringToInt("-" + intToString(-n));
        0 - stringToInt(intToString(-n));
        { intToStringThenStringToIntIdem(-n); }
        n;
      }
    } else if 0 <= n <= 9 {
      assert stringToInt(intToString(n)) == n;
    } else {
      assert intToString(n) == intToString(n / 10) + intToString(n % 10);
      var s := intToString(n);
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

  lemma stringToIntNonnegative(s: string)
    requires IsStringInt(s)
    requires s[0] != '-'
    decreases |s|
    ensures 0 <= stringToInt(s)
    ensures s != "0" ==> 0 < stringToInt(s)
    ensures |s| > 1 ==> 10 <= stringToInt(s)
  {
    if |s| == 0 {

    } else if |s| == 1 {
      reveal digitToInt(), stringToInt(), IsStringInt();
      match s[0]
      case '0' => case '1' => case '2' => case '3' => case '4' =>
      case '5' => case '6' => case '7' => case '8' => case '9' =>
      case _ =>
    } else if s[0] == '-' {
    } else {
      assert !(|s|  == 0 || |s| == 1 || s[0] == '-');
      reveal stringToInt();
      assert stringToInt(s) == stringToInt(s[0..|s|-1])*10 + stringToInt(s[|s|-1..|s|]);
      assert IsStringInt(s[0..|s|-1]) by {
        reveal IsStringInt();
      }
      stringToIntNonnegative(s[..|s|-1]);
      var tail := s[|s|-1..|s|];
      assert IsStringInt(tail) && tail[0] != '-' by {
        reveal IsStringInt();
      }
      stringToIntNonnegative(tail);
      reveal IsStringInt();
      assert |s| > 1 ==> 10 <= stringToInt(s);
    }
  }

  lemma stringToIntThenIntToStringIdem(s: string)
    requires IsStringInt(s)
    decreases |s|
    ensures s[0] != '-' ==> 0 <= stringToInt(s)
    ensures |s| == 1 ==> 0 <= stringToInt(s) <= 9
    ensures intToString(stringToInt(s)) == s
  {
    assert |s| > 0;
    if 1 <= |s| && s[0] == '-' {
      reveal intToString(), stringToInt(), IsStringInt();
      assert forall i | 1 <= i < |s| :: s[i] in "0123456789";
      calc {
        intToString(stringToInt(s));
        intToString(0 - stringToInt(s[1..]));
      }
    } else if |s| == 1 {
      reveal intToString(), stringToInt(), IsStringInt(), digitToInt();
      calc {
        intToString(stringToInt(s));
        s;
      }
    } else {
      var n := stringToInt(s);
      stringToIntNonnegative(s);
      var init := s[..|s|-1];
      var last := s[|s|-1..|s|];
      var q := stringToInt(init);
      var r := stringToInt(last);
      assert IsStringInt(init) by { reveal IsStringInt(); }
      assert IsStringInt(last) by { reveal IsStringInt(); }
      stringToIntThenIntToStringIdem(init);
      stringToIntThenIntToStringIdem(last);
      assert stringToInt(s) ==
             stringToInt(s[0..|s|-1])*10 + stringToInt(s[|s|-1..|s|]) by {
        reveal stringToInt();
      }
      assert n == q * 10 + r;
      calc {
        intToString(n);
        { reveal intToString();
          assert !(n < 0);
          assert n != 0;
        }
        intToString(n / 10) + intToString(n % 10);
        s;
      }
    }
  }
}
