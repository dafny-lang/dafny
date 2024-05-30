// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype uint8 = x: int | 0 <= x < 0x100

function ConversionSatisfiesConstraints(i: int): uint8
{
    i as uint8
}