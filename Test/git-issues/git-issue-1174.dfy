// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function fm1(): bool
{
    (true)
}

function method fm2():bool
{
    var v := fm1();
    (v)
}

