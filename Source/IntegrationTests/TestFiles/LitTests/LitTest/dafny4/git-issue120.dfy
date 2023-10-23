// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function {:opaque} opfn(): int { 37 }

ghost function foo(): int
{
    var x := opfn();
    assert x == 37 by { reveal opfn(); }
    x
}

