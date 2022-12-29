// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
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
