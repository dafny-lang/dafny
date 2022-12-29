// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Foo {
    // this is accepted
    constructor(ghost b: set<bool>) {}
    constructor Mk() {}
    method Initialize(ghost b: set<bool>) {}
}

method TestConstructor() {
    ghost var b: set<bool> := {};
    var f := new Foo(b);
    // error: ghost variables are only allowed in specification contexts
}

method TestInitialize() {
    ghost var b: set<bool> := {};
    var f := new Foo.Mk();
    // works
    f.Initialize(b);
}

