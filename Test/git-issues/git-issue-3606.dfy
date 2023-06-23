// RUN: %exits-with 2 %dafny /compile:0 /functionSyntax:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C { }

function F(): int
  // The following is disallowed, since the set comprehension depends on the allocation state (via c).
  // That would make F depend on the allocation state, which is not allowed.
  reads set c: C, obj: object | obj in M(c) :: obj // error: depends on allocation state

function G(): int
  // The following is also disallowed, since it is equivalent to the reads clause of F.
  reads M // error: depends on allocation state
{
  5
}

function M(x: C): set<object> {
  {x}
}

ghost method Test()
  ensures false
{
  var gr := G.reads();
  var c := new C;
  assert c in M(c);
  assert c in gr;
}
