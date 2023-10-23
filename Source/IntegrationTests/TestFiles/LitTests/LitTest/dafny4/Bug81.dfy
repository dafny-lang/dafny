// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function {:opaque} RefineSeqToSeq<T(!new), U>(s:seq<T>, refine_func: T ~> U) : seq<U>
{
  if |s| == 0 then []
  else RefineSeqToSeq(s[1..], refine_func)
}
