// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"
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

