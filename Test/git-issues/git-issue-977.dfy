// RUN: %dafny /compile:0 /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Option<V> = Some(value: V) | None

predicate IsGoodInt(x: int)
{
  && 0 <= x
  && x != 5  // related location
}

predicate IsGoodOpt_Impl(opt: Option<int>)
{
  && (opt.Some? ==> IsGoodInt(opt.value))  // related location
  && (opt.None? ==> true)
}

predicate IsGoodOpt_IfThenElse(opt: Option<int>)
{
  if opt.Some? then
    var x := opt.value;
    IsGoodInt(x)
  else
    true
}

predicate IsGoodOpt_Match(opt: Option<int>)
{
  match opt {
    case Some(x) => IsGoodInt(x)  // related location
    case None => true
  }
}

method Main() {
  var x := Some(5);
  if
  case true =>
    assert IsGoodOpt_Impl(x);  // error
  case true =>
    assert IsGoodOpt_IfThenElse(x);  // error
  case true =>
    assert IsGoodOpt_Match(x);  // error
}

// ----- Regression tests --------------------------------------------------------

datatype Number = Succ(prev: Number) | Zero

function ToNumber(n: nat): Number {
  if n == 0 then Zero else Succ(ToNumber(n - 1))
}

lemma About_Num(num: Number)
  ensures Pred(num)
  ensures GreatestPredOrd(num)
  ensures GreatestPredNat(num)
{
}

lemma About_NumOrd(k: ORDINAL, num: Number)
  ensures GreatestPredOrd#[k](num)
  ensures GreatestManualOrd(k, num)
  ensures RicochetOrd(k, num)
{
  if k.IsSucc {
    match num
    case Succ(prev) => About_NumOrd(k - 1, prev);
    case Zero =>
  } else {
    forall m | m < k {
      About_NumOrd(m, num);
    }
  }
}

lemma About_NumNat(k: nat, num: Number)
  ensures GreatestPredNat#[k](num)
  ensures GreatestManualNat(k, num)
  ensures RicochetNat(k, num)
{
}

predicate Pred(num: Number) {
  match num
  case Succ(prev) => Pred(prev)
  case Zero => true
}
lemma Test0(n: int)
{
  About_Num(ToNumber(if n < 0 then 0 else n));
  assert Pred(ToNumber(if n < 0 then 0 else n));  // info: not inlined
}

greatest predicate GreatestPredOrd(num: Number) {
  match num
  case Succ(prev) => GreatestPredOrd(prev)
  case Zero => true
}
lemma Test1(n: int)
{
  About_Num(ToNumber(if n < 0 then 0 else n));
  assert GreatestPredOrd(ToNumber(if n < 0 then 0 else n));  // info: not inlined
}
lemma Test2(k: ORDINAL, n: int)
{
  About_NumOrd(k, ToNumber(if n < 0 then 0 else n));
  // Regression test: The following line once caused the "n < 0" to be inlined inside
  // a quantifier, which is malformed Boogie.
  assert GreatestPredOrd#[k](ToNumber(if n < 0 then 0 else n));  // info: not inlined
}

greatest predicate GreatestPredNat[nat](num: Number) {
  match num
  case Succ(prev) => GreatestPredNat(prev)
  case Zero => true
}
lemma Test3(n: int)
{
  About_Num(ToNumber(if n < 0 then 0 else n));
  assert GreatestPredNat(ToNumber(if n < 0 then 0 else n));  // info: not inlined
}
lemma Test4(k: nat, n: int)
{
  About_NumNat(k, ToNumber(if n < 0 then 0 else n));
  assert GreatestPredNat#[k](ToNumber(if n < 0 then 0 else n));  // info: not inlined
}

predicate GreatestManualOrd(k: ORDINAL, num: Number)
{
  if k == 0 then
    true
  else if k.IsSucc then
    match num
    case Succ(prev) => GreatestManualOrd(k - 1, prev)
    case Zero => true
  else
    forall m :: m < k ==> GreatestManualOrd(m, num)
}
lemma Test5(k: ORDINAL, n: int)
{
  About_NumOrd(k, ToNumber(if n < 0 then 0 else n));
  assert GreatestManualOrd(k, ToNumber(if n < 0 then 0 else n));  // info: not inlined
}

predicate GreatestManualNat(k: nat, num: Number)
{
  if k == 0 then
    true
  else
    match num
    case Succ(prev) => GreatestManualNat(k - 1, prev)
    case Zero => true
}
lemma Test10(k: nat, n: int)
{
  About_NumNat(k, ToNumber(if n < 0 then 0 else n));
  assert GreatestManualNat(k, ToNumber(if n < 0 then 0 else n));  // info: not inlined
}

predicate RicochetOrd(k: ORDINAL, n: Number) {
  GreatestPredOrd#[k](n)  // info: not inlined
}
lemma Test6(k: ORDINAL, n: int)
{
  About_NumOrd(k, ToNumber(if n < 0 then 0 else n));
  // Regression test: The following line once caused the "n < 0" to be inlined inside
  // a quantifier, which is malformed Boogie.
  assert RicochetOrd(k, ToNumber(if n < 0 then 0 else n));  // info: not inlined
}

predicate RicochetNat(k: nat, n: Number) {
  GreatestPredNat#[k](n)  // info: not inlined
}
lemma Test7(k: nat, n: int)
{
  About_NumNat(k, ToNumber(if n < 0 then 0 else n));
  assert RicochetNat(k, ToNumber(if n < 0 then 0 else n));  // info: not inlined
}

// ----- Inline/trigger issues for prefix predicates --------------------------------------------------------

module PrefixBodyInlining {
  greatest predicate AAA(r: nat)
  {
    BBB(r)
  }

  greatest predicate BBB(s: nat)

  lemma P(k: ORDINAL, n: int)
    requires forall t :: AAA#[k](t)
  {
    // We DO NOT want the following call to be inlined--a trigger would then contain a "<".
    assert AAA#[k](if n < 0 then 0 else n); // info: not inlined
  }



  codatatype IList = ICons(head: int, tail: IList)

  function UpIList(n: int): IList
  {
    ICons(n, UpIList(n+1))
  }

  greatest predicate Pos(s: IList)
  {
    s.head > 0 && Pos(s.tail)
  }

  greatest lemma {:induction false} Theorem2(n: int)
    requires 1 <= n
    ensures Pos(UpIList(n)) // We DO want this call to be inlined--needed to prove the lemma.
  {
    Theorem2(n+1);
  }
}
