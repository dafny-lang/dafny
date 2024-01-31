// RUN: ! %baredafny test --use-basename-for-filename --show-snippets:false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method {:test} M(x: int) returns (r: int)
{
    expect x != x;
    return x;
}
