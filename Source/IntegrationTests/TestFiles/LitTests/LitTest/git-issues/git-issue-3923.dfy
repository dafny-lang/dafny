// RUN: %exits-with 4 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method DoSomething() {
}

datatype Fruit = Apple(u: int) | Pear(t: int)

method Abc(fruit: Fruit)
{
  match fruit
  case Apple(x) =>
    DoSomething();
  case _  =>
}

method Def(fruit: Fruit)
{
  match fruit
  case Apple(_) =>
    DoSomething();
  case _  =>
}

method Ghi(fruit: Fruit)
{
  match fruit
  case Apple(x: int) =>
    DoSomething();
  case _  =>
}

method Jkl(fruit: Fruit)
{
  match fruit
  case Apple(_: int) => // this once caused Dafny to crash
    DoSomething();
  case _  =>
}

method Mno(fruit: Fruit)
{
  match fruit
  case Apple(x: nat) => // error: cannot prove that the value of x is a nat
    DoSomething();
  case _  =>
}

method Pqr(fruit: Fruit)
{
  match fruit
  // the next line once caused Dafny to crash
  case Apple(_: nat) => // error: cannot prove that the value of _ is a nat
    DoSomething();
  case _  =>
}

method Stu(fruit: Fruit)
  requires fruit.Apple? ==> 0 <= fruit.u
{
  match fruit
  case Apple(x: nat) =>
    DoSomething();
  case _  =>
}

method Vwx(fruit: Fruit)
  requires fruit.Apple? ==> 0 <= fruit.u
{
  match fruit
  case Apple(_: nat) => // this once caused Dafny to crash
    DoSomething();
  case _  =>
}
