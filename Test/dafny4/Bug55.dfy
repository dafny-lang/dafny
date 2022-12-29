// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate {:opaque} G(f:int~>bool)
  reads f.reads;
  requires f.requires(0);
{
  true
}

predicate A<T>(s:set<T>)

predicate{:opaque} B(s:set<int>)
    requires A(s);
