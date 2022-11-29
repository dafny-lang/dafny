// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Foo() returns (i: int) {
    return "hello";
}

function foo(): int {
    "hello"
}
