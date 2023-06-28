// RUN: ! %baredafny test --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method {:test} M() returns (r: int)
{
    expect 0 != 0;
    return 0;
}
