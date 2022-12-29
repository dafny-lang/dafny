// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Jug()
{
  var x, y, z;
  while x > 0 && y > 0 && z > 0
    decreases x < y, z
  {
    if y > x {
      y := z;
      x := *;
      z := x - 1;
    } else {
      z := z - 1;
      x := *;
      y := x - 1;
    }
  }
}
