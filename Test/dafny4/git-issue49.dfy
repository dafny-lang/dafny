// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module m1 {
 export reveals f

 type T = int
 function f(x:T) : T { x }
}
