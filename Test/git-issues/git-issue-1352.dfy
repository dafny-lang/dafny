// RUN: %baredafny build --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function fm(b: int): int { 0 }

predicate pm(a: int)
{
    true
}

function fm'(n: int): int
ensures pm(n)
{
    var v := fm(n);
    //assert pm(v);   // OK
    //assume pm(v);   // OK
    expect pm(v);   // error
    v
}

