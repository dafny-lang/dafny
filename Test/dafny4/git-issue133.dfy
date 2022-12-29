// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype State = State(m:map<int, bool>)

lemma Test(s:State)
  requires 42 in s.m
  ensures s.(m := s.m[42 := s.m[42]]) == s
{
  var s' := s.(m := s.m[42 := s.m[42]]);
  assert s'.m == s.m;
}

datatype MyDt = MakeA(x: int, bool) | MakeB(s: multiset<int>, t: State)

lemma AnotherTest(a: MyDt, b: MyDt, c: bool)
  requires a.MakeB? && b.MakeB?
  requires a.s == multiset(a.t.m.Keys) && |b.s| == 0
  requires a.t.m == map[] && |b.t.m| == 0
{
  assert a == b;
}

datatype GenDt<X,Y> = Left(X) | Middle(X,int,Y) | Right(y: Y)

method ChangeGen(g: GenDt)
{
  match g
  case Left(_) =>
  case Middle(_,_,_) =>
  case Right(u) =>
    var h := g.(y := u);
    assert g == h;
}

datatype Recursive<X> = Red | Green(next: Recursive, m: set)

lemma RecLem(r: Recursive) returns (s: Recursive)
  ensures r == s
{
  match r
  case Red =>
    s := Red;
  case Green(next, m) =>
    var n := RecLem(next);
    s := Green(n, m + m);
}
