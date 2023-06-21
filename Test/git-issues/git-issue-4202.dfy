// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

opaque function F(x: int): char
{ 'D' }

method InitArray<D>(f: int -> D) returns (a: D)
{
  return f(44);
}

method Main() {
  reveal F();
  var c := InitArray(F);
}