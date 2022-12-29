// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:opaque} opfn(): int { 37 }

function foo(): int
{
    var x := opfn();
    assert x == 37 by { reveal opfn(); }
    x
}

