// RUN: %testDafnyForEachResolver "%s"


ghost function {:opaque} RefineSeqToSeq<T(!new), U>(s:seq<T>, refine_func: T ~> U) : seq<U>
  reads refine_func.reads
{
  if |s| == 0 then []
  else RefineSeqToSeq(s[1..], refine_func)
}
