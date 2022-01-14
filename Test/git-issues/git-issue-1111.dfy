// RUN: %dafny /compileTarget:java "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Foo {
    class A {

        const a : int
        const b : int

        constructor(k : int, j : int)
        {
            //a := k;
            //b := j;
            a, b := k, j;
        }
    }
    method Main()
    {
        var o := new A(1, 2);
    }
}