// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function fm1(): bool
{
    (true)
}

function fm2():bool
{
    var v := fm1();
    (v)
}

