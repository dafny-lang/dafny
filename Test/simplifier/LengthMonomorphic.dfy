// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List = Nil | Cons(car: nat, cdr: List)

function {:simplifier} simp<T>(t: T): T { t }

function method {:opaque} Length(xs: List): nat
{
  match xs
    case Nil => 0
    case Cons(x, xs') => 1 + Length(xs')
}

lemma {:simp} Length_simp(x: nat, xs: List)
  ensures Length(Cons(x, xs)) == 1 + Length(xs)
{
  reveal Length();
}

lemma {:simp} Length_nil_simp()
  ensures Length(Nil) == 0
{
  reveal Length();
}

function Length2(x: nat, y: nat): nat
{
  simp(Length(Cons(x, Cons(y, Nil))))
}

lemma Length2_2(x: nat, y: nat)
  ensures Length2(x, y) == 2
{
}
