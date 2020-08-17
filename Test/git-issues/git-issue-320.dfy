class C {
  var a: array<nat>
  var n: nat

  method f()
    modifies a
    requires n < a.Length
    ensures a[..] == old(a[..n]) + [0] + old(a[n+1..])
  {
    a[n] := 0;
  }

  method g()
    modifies a
    requires n < a.Length
    ensures a[..] == old(a)[..old(n)] + [0] + old(a)[old(n)+1..]
  {
    a[n] := 0;
  }

  method h()
    modifies a
    requires n < a.Length
    ensures a[..] == old(a[..n]) + [0] + old(a[n+1..])
  {
    a[n] := 0;
  
}

}


method m(g1: C, g2: C, g3: C)
  requires g1 != g2 && g1.a != g2.a
  requires g2 != g3 && g2.a != g3.a
  requires g1 != g3 && g1.a != g3.a
  requires g1.n < g1.a.Length
  requires g1.a[..] == g2.a[..] == g3.a[..]
  requires g1.n == g2.n == g3.n
  modifies g1.a, g2.a, g3.a
{
  g1.f();
  g2.g();
  g3.h();
  assert g1.a[..] == g2.a[..];
  assert g1.a[..] == g3.a[..];
}

