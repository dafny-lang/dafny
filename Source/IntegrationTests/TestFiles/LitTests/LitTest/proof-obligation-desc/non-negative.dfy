// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function NonNegative(): seq<int>
{
    seq(-1, i => 0)
}