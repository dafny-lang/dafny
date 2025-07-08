// RUN: %baredafny test --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method {:test} M() returns (r: int)
{
    return 0;
}
