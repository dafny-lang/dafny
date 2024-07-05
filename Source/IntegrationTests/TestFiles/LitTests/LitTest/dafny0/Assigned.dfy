// RUN: %verify --relax-definite-assignment "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C<G>
{
  var x: G
  const y: G
  
  constructor Con0(i: int, a: G, b: G)
  {
    x := a;
    y := b;
    assert assigned(x);
    assert assigned(y);
    new;
    if i > 0 {
      x := y;
    }
  }
  
  constructor Con1(i: int, a: G, b: G)
  {
    x := a;
    assert assigned(x);
    assume {:axiom} assigned(y);
    new;
    if i > 0 {
      x := y;
    }
  }
}

method M0<G>(x: int, a: G, b: G) returns (y: G)
{
  if x < 10 {
    y := a;
  } else if x < 20 {
    return b;
  } else {
    assume {:axiom} assigned(y);
  }
}
