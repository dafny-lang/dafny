codatatype Stream<T> = Cons(head: T, tail: Stream);

function Upward(n: int): Stream<int>
{
  Cons(n, Upward(n + 1))
}

copredicate Pos(s: Stream<int>)
{
  0 < s.head && Pos(s.tail)
}

function Doubles(n: int): Stream<int>
{
  Cons(2*n, Doubles(n + 1))
}

copredicate Even(s: Stream<int>)
{
  s.head % 2 == 0 && Even(s.tail)
}

ghost method Lemma0(n: int)
  ensures Even(Doubles(n));
{
}

function UpwardBy2(n: int): Stream<int>
{
  Cons(n, UpwardBy2(n + 2))
}

ghost method Lemma1(n: int)
  ensures Even(UpwardBy2(2*n));  // error:  this is true, but Dafny can't prove it
{
}

function U2(n: int): Stream<int>
  requires n % 2 == 0;
{
  UpwardBy2(n)
}

ghost method Lemma2(n: int)
  ensures Even(UpwardBy2(2*n));  // this is true, but Dafny can't prove it
{
  assert Even(U2(2*n));  // ... thanks to this lemma
}
