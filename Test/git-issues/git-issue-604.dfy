// RUN: %dafny "%s" /compile:3 /compileTarget:cs > "%t"
// RUN: %dafny "%s" /compile:3 /compileTarget:js > "%t"
// RUN: %dafny "%s" /compile:3 /compileTarget:java > "%t"
// RUN: %dafny "%s" /compile:3 /compileTarget:go > "%t"
// RUN: %diff "%s.expect" "%t"

method Inv() returns (x: int) {
    x := 0;
    while x < 100
        invariant 0 <= x <= 100
    assert x == 25;
    return x;
}
