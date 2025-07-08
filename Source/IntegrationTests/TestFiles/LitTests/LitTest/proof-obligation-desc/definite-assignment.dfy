// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C<G>
{
  var x: G
  const y: G
  
  constructor Con0(i: int, a: G, b: G)
  {
    if i > 0 {
      x := a;
    } else {
      y := b;
    }
    new;
    if i > 10 {
      x := y;
    }
  }
}

method M0<G>(i: int, a: G, b: G) returns (x: G, y: G)
{
  if i < 0 {
    x := a;
  } else if i < 10 {
    y := b;
  } else if i < 20 {
    x := a;
    y := x;
  } else if i < 30 {
    x := y;
    y := b;
  }
}

method M1<G>(i: int, a: G, b: G) returns (x: G, y: G)
{
  if i < 0 {
    return x, y;
  }
  return a, b;
}

method M2<G>(i: int, a: G, b: G) returns (x: G, y: G)
{
  if i < 0 {
    x := a;
    return x, y;
  }
  return a, b;
}

method M3<G>(i: int, a: G, b: G, c: G) returns (x: G, y: G, z: G)
{
  if i < 0 {
    x := y;
    return x, y, z;
  }
  return a, b, c;
}

method M4<G>(i: int, a: G, b: G) returns (x: G, y: G)
{
  if i < 0 {
    x := a;
    return;
  }
  return a, b;
}

method M5<G>(i: int, a: G, b: G, c: G) returns (x: G, y: G, z: G)
{
  if i < 0 {
    x := y;
    return;
  }
  return a, b, c;
}

method M6<G>(i: int, a: G, b: G) returns (x: G, y: G)
{
  if i < 0 {
    x, y := y, x;
    return;
  }
  return a, b;
}
