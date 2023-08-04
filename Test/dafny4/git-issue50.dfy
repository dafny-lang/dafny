// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module am {
 type T
}

module cm1 refines am {
 export reveals f
 type T = int

 ghost function f(i:int) : int { i }
}

module cm2 refines am {
 import opened cm1
 type T = bool

 ghost function g(b:T) : T { !b } // Error incorrectly reported here
}

module m {
 import opened cm1

 ghost function h(t:T) : int { t + 1 } // Error correctly reported here
}
