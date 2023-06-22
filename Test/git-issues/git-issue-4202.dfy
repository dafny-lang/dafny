// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

opaque function F(x: int): char
{ 'D' }

function InitArray<D>(f: int -> D): (a: D)
{
  f(44)
}

method Main() {
  reveal F();
  var c := InitArray(F);
  assert c == 'D';
}