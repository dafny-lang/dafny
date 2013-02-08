function f(x: int, y: int): int

ghost method Associativity(x: int, y: int, z: int)
  ensures f(x, f(y, z)) == f(f(x, y), z);

ghost method Monotonicity(y: int, z: int)
  requires y <= z;
  ensures forall x :: f(x, y) <= f(x, z);

ghost method DiagonalIdentity(x: int)
  ensures f(x, x) == x;

method M(a: int, b: int, c: int, x: int)
  requires c <= x == f(a, b);
{
  calc {
    f(a, f(b, c));
    { Associativity(a, b, c); }
    f(f(a, b), c);
    { assert f(a, b) == x; }
    f(x, c);
    <= { assert c <= x; Monotonicity(c, x); }
    f(x, x);
    { DiagonalIdentity(x); }
    x;
  }
}
