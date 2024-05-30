// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function ConversionIsNatural(ord: ORDINAL): int
{
    ord as int
}