// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function BitsAsInt(b:bv32): int
    ensures 0 <= BitsAsInt(b) < 0x1_0000_0000
{
    b as int
}
