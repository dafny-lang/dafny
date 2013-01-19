codatatype Stream<T> = Cons(head: T, tail: Stream);

function Upward(n: int): Stream<int>
{
  Cons(n, Upward(n + 1))
}

copredicate Pos(s: Stream<int>)
{
  0 < s.head && Pos(s.tail)
}

comethod {:induction false} PosLemma0(n: int)
  requires 1 <= n;
  ensures Pos(Upward(n));
{
  PosLemma0(n + 1);  // this completes the proof
}

comethod {:induction false} PosLemma1(n: int)
  requires 1 <= n;
  ensures Pos(Upward(n));
{
  PosLemma1(n + 1);
  if (*) {
    assert Pos(Upward(n + 1));  // error: cannot conclude this here, because we only have prefix predicates
  }
}

comethod {:induction false} Outside_CoMethod_Caller_PosLemma(n: int)
  requires 1 <= n;
  ensures Pos(Upward(n));
{
  assert Upward(n).tail == Upward(n + 1);  // follows from one unrolling of the definition of Upward
  PosLemma0(n + 1);
  assert Pos(Upward(n+1));  // this follows directly from the previous line, because it isn't a recursive call
  // ... and it implies the prefix predicate we're supposed to establish
}

method Outside_Method_Caller_PosLemma(n: int)
  requires 1 <= n;
  ensures Pos(Upward(n));  // this method postcondition follows just fine
{
  assert Upward(n).tail == Upward(n + 1);  // follows from one unrolling of the definition of Upward
  PosLemma0(n + 1);
  assert Pos(Upward(n+1));  // this follows directly from the previous line, because it isn't a recursive call
}

copredicate X(s: Stream)  // this is equivalent to always returning 'true'
{
  X(s)
}

comethod {:induction false} AlwaysLemma_X0(s: Stream)
  ensures X(s);  // prove that X(s) really is always 'true'
{  // error: this is not the right proof
  AlwaysLemma_X0(s.tail);
}

comethod {:induction false} AlwaysLemma_X1(s: Stream)
  ensures X(s);  // prove that X(s) really is always 'true'
{
  AlwaysLemma_X1(s);  // this is the right proof
}

comethod {:induction false} AlwaysLemma_X2(s: Stream)
  ensures X(s);
{
  AlwaysLemma_X2(s);
  if (*) {
    assert X(s);  // error: cannot conclude the full predicate here
  }
}

copredicate Y(s: Stream)  // this is equivalent to always returning 'true'
{
  Y(s.tail)
}

comethod {:induction false} AlwaysLemma_Y0(s: Stream)
  ensures Y(s);  // prove that Y(s) really is always 'true'
{
  AlwaysLemma_Y0(s.tail);  // this is a correct proof
}

comethod {:induction false} AlwaysLemma_Y1(s: Stream)
  ensures Y(s);
{  // error: this is not the right proof
  AlwaysLemma_Y1(s);
}

comethod {:induction false} AlwaysLemma_Y2(s: Stream)
  ensures Y(s);
{
  AlwaysLemma_Y2(s.tail);
  if (*) {
    assert Y(s.tail);  // error: not provable here
  }
}

copredicate Z(s: Stream)
{
  false
}

comethod {:induction false} AlwaysLemma_Z(s: Stream)
  ensures Z(s);  // says, perversely, that Z(s) is always 'true'
{  // error: this had better not lead to a proof
  AlwaysLemma_Z(s);
}

function Doubles(n: int): Stream<int>
{
  Cons(2*n, Doubles(n + 1))
}

copredicate Even(s: Stream<int>)
{
  s.head % 2 == 0 && Even(s.tail)
}

comethod {:induction false} Lemma0(n: int)
  ensures Even(Doubles(n));
{
  Lemma0(n+1);
}

function UpwardBy2(n: int): Stream<int>
{
  Cons(n, UpwardBy2(n + 2))
}

comethod {:induction false} Lemma1(n: int)
  ensures Even(UpwardBy2(2*n));
{
  Lemma1(n+1);
}

comethod {:induction false} ProveEquality(n: int)
  ensures Doubles(n) == UpwardBy2(2*n);
{
  ProveEquality(n+1);
}

comethod {:induction false} BadEquality0(n: int)
  ensures Doubles(n) == UpwardBy2(n);
{  // error: postcondition does not hold
  BadEquality0(n+1);
}

comethod {:induction false} BadEquality1(n: int)
  ensures Doubles(n) == UpwardBy2(n+1);
{  // error: postcondition does not hold
  BadEquality1(n+1);
}

// test that match statements/expressions get the correct assumption (which wasn't always the case)

codatatype IList<T> = INil | ICons(head: T, tail: IList<T>);

ghost method M(s: IList)
{
  match (s) {
    case INil =>
      assert s == INil;
    case ICons(a, b) =>
      assert s == ICons(a, b);
  }
}

function G(s: IList): int
{
  match s
  case INil =>
    assert s == INil;
    0
  case ICons(a, b) =>
    assert s == ICons(a, b);
    0
}
