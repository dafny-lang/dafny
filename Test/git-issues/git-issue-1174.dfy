// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
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

