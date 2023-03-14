// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function {:opaque} Reverse(id:int) : int

ghost function RefineToMap(ReverseKey:int->int) : bool

ghost function RefineToMapOfSeqNums() : bool
{
    RefineToMap(Reverse)
}
