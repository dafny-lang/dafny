// RUN: %exits-with 2 %verify --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Foo() returns (i: int) {
    i := "explicit assignment";
    return "implicit assignment";
}

ghost function foo(): int {
    "hello"
}
