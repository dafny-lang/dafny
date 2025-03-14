// RUN: %testDafnyForEachCompiler "%s" -- --type-system-refresh=false --general-newtypes=false --relax-definite-assignment

datatype S = S(G: array<int>)
datatype T = T(F: array<S>, ghost Repr: set<object>)

ghost predicate Valid(t: T)
  reads t.F
  reads (set i | 0 <= i < t.F.Length :: t.F[i].G)
{
  var short := t.F;
  t.Repr == (set i | 0 <= i < short.Length :: short[i].G) + {short}
}

method Main() {
}
