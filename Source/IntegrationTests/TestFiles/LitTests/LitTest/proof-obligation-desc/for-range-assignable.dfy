// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method ForRangeAssignable()
{
    for i: nat := -1 to 0 {}
}