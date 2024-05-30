// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function ShiftLowerBound(b: bv2): bv2 {
    b.RotateLeft(-1)
}