// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function ConversionPositive(i: int): ORDINAL
{
    i as ORDINAL
}