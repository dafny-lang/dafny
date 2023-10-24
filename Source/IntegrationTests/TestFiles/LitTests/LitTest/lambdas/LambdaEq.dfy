// RUN: %exits-with 4 %dafny /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma Eq1(b: bool)
{
  var f: nat -> int := (x: nat) => x;
  var g: int -> int := (x: int) => x;
  var h: int -> int := (x: int) => x;
  assert g == h; // should pass
  assert f == g; // should fail because f's and g's domains are different
}

lemma Eq2(b: bool)
{
  var f: nat -> int := (x: nat) => x;
  var i: nat -> int := (x: int) => x;
  assert f == i; // should fail because f's and i's actual domains are different
}
