// RUN: %testDafnyForEachResolver "%s"


ghost function BitvectorCast(x:bv32): int
    ensures x != 0 ==> BitvectorCast(x) != 0
{
    x as int
}
