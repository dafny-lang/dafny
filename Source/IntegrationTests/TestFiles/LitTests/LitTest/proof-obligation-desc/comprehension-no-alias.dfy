// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function ComprehensionNoAlias(i: nat, j: nat): map<int, nat>
{
    map x: nat, y: nat | x < i && y < j :: x + y := x
}