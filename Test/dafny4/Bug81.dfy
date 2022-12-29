// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:opaque} RefineSeqToSeq<T,U>(s:seq<T>, refine_func:T~>U) : seq<U>
    reads refine_func.reads;
{
    if |s| == 0 then []
    else RefineSeqToSeq(s[1..], refine_func)
}
