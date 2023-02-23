// RUN: %dafny /dafnyVerify:0 /compile:0 /env:0 /rprint:"%t.dfy" "%s"
// RUN: %dafny /dafnyVerify:0 /compile:0 /env:0 /printMode:DllEmbed /rprint:"%t1.dfy" "%t.dfy"
// RUN: %dafny /env:0 /compile:3 /printMode:DllEmbed /rprint:"%t2.dfy" "%t1.dfy" > "%t"
// RUN: %diff "%t1.dfy" "%t2.dfy"
// RUN: %diff "%s.expect" "%t"

datatype List<T> = Nil | Cons(car: T, cdr: List)

function funkyNil(l: List): List
{
  match l
  case Cons(x,y) => funkyNil(y)
  case Nil => l
}

method H(a: array, l: List)
{
  match l
  case Cons(x,y) =>
    if a.Length > 0 && a[0] == x {
    }
  case Nil =>
}

method Main() {
  var xs := Cons(28, Cons(22, Cons(28, Cons(5, Nil))));
  var a := new [][60, 60];
  var nil := funkyNil(xs);
  H(a, xs);
  print nil, "\n";
}
