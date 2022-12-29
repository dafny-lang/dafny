// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype S = S(G: array<int>)
datatype T = T(F: array<S>, ghost Repr: set<object>)

predicate Valid(t: T)
  reads t.F
  reads (set i | 0 <= i < t.F.Length :: t.F[i].G)
{
  var short := t.F;
  t.Repr == (set i | 0 <= i < short.Length :: short[i].G) + {short}
}

method Main() {
}
