//XFAIL: *
//RUN: %dafny /dafnyVerify:0 /compile:0 /env:0 /dprint:"%t.dfy" "%s"
//RUN: %dafny /dafnyVerify:0 /compile:0 /env:0 "%t.dfy" > "%t.output"
//RUN: %diff "%s.expect" "%t.output"

datatype List<T> = Nil | Cons(car: T, cdr: List)

function method funkyNil(l : List): List
{
  match l { 
     case Cons(x,y) => funkyNil(y)
     case Nil => l 
  }
}

