// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
ghost function f(x: int, y: int): int

lemma {:axiom} Associativity(x: int, y: int, z: int)
  ensures f(x, f(y, z)) == f(f(x, y), z)

lemma {:axiom} Monotonicity(y: int, z: int)
  requires y <= z
  ensures forall x :: f(x, y) <= f(x, z)

lemma {:axiom} DiagonalIdentity(x: int)
  ensures f(x, x) == x

// From these axioms, we can prove a lemma about "f":

method CalculationalStyleProof(a: int, b: int, c: int, x: int)
  requires c <= x == f(a, b)
  ensures f(a, f(b, c)) <= x
{
  calc == {
    f(a, f(b, c));
    { Associativity(a, b, c); }
    f(f(a, b), c);
    { assert f(a, b) == x; }
    f(x, c);
    { assert c <= x; Monotonicity(c, x); }
    // Error, because the relation here should be <=, not ==
    f(x, x);
    { DiagonalIdentity(x); }
    x;
  }
}

method NoHintProof(x: int) {
  calc == {
    x - 1 + 1;
    x + 1;
  }
}
