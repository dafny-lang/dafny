// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function OrdinalSubtractionUnderflow(o0: ORDINAL, o1: ORDINAL): ORDINAL
    requires o1.IsNat
{
    o0 - o1
}