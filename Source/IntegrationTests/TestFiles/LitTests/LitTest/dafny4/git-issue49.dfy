// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


module m1 {
 export reveals f

 type T = int
 ghost function f(x:T) : T { x }
}
