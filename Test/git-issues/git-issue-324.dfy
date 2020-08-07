// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

abstract module Sig {
    class Foo {
        const v: int
        constructor () {}
        method hi()
    }
}

module Impl1 refines Sig {
    class Foo {
        const v := 42
        constructor () {}
        method hi() {
            print "Hello!\n";
        }
    }
}

module Program {
    import opened Impl1: Sig

    method Main() {
        var f := new Foo();
        // as expected, we get an assertion violation here because
        // the value of v is not specified in Sig
        // assert f.v == 42;
        f.hi();
    }
}

