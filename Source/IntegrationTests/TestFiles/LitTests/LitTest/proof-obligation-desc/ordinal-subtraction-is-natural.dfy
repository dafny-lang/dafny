// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function OrdinalSubtractionIsNatural(o0: ORDINAL, o1: ORDINAL): ORDINAL
    requires o1.Offset <= o0.Offset
{
    o0 - o1
}