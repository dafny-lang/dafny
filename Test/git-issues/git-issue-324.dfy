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

