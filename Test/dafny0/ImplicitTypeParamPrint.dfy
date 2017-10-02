//RUN: %dafny /dafnyVerify:0 /compile:0 /env:0 /rprint:"%t.dfy" "%s"
//RUN: %dafny /dafnyVerify:0 /compile:0 /env:0 /printMode:DllEmbed /rprint:"%t1.dfy" "%t.dfy"
//RUN: %dafny /env:0 /out:"%s.dll" /printMode:DllEmbed /rprint:"%t2.dfy" "%t1.dfy" > "%t.output"
//RUN: %diff "%t1.dfy" "%t2.dfy"
//RUN: %diff "%t.output" "%s.expect"

datatype List<T> = Nil | Cons(car: T, cdr: List)

function method funkyNil(l: List): List
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

