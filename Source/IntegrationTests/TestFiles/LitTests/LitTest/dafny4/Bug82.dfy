// RUN: %testDafnyForEachResolver "%s"


ghost opaque function Reverse(id: int): int

ghost function RefineToMap(ReverseKey: int -> int): bool

ghost function RefineToMapOfSeqNums(): bool
{
  RefineToMap(Reverse)
}
