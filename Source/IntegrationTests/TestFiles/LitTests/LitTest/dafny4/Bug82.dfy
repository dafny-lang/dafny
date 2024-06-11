// RUN: %testDafnyForEachResolver "%s"


ghost function {:opaque} Reverse(id:int) : int

ghost function RefineToMap(ReverseKey:int->int) : bool

ghost function RefineToMapOfSeqNums() : bool
{
    RefineToMap(Reverse)
}
