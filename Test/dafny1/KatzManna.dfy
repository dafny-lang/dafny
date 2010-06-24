method NinetyOne(x: int) returns (z: int)
  requires 0 <= x;
//  ensures z == (if x > 101 then x-10 else 91);
{
  var y1 := x;
  var y2 := 1;
  while (true)
    invariant (y1 <= 111 && y2 >= 1) || (y1 == x && y2 == 1);
    decreases -2*y1 + 21*y2 + 2*(if x < 111 then 111 else x);
  {
    if (y1 > 100) {
      if (y2 == 1) {
        break;
      } else {
        y1 := y1 - 10;
        y2 := y2 - 1;
      }
    } else {
      y1 := y1 + 11;
      y2 := y2 + 1;
    }
  }
  z := y1 - 10;
}

method Gcd(x1: int, x2: int)
  requires 1 <= x1 && 1 <= x2;
{
  var y1 := x1;
  var y2 := x2;
  while (y1 != y2)
    invariant 1 <= y1 && 1 <= y2;
    decreases y1 + y2;
  {
    while (y1 > y2)
      invariant 1 <= y1 && 1 <= y2;
    {
      y1 := y1 - y2;
    }
    while (y2 > y1)
      invariant 1 <= y1 && 1 <= y2;
    {
      y2 := y2 - y1;
    }
  }
}

method Determinant(X: Matrix, M: int) returns (z: int)
  requires 1 <= M;
  requires X != null && M == X.Size;
{
  var y := X.Get(1,1);
  var a := 1;
  while (a != M)
    invariant 1 <= a && a <= M;
  {
    var b := a + 1;
    while (b != M+1)
      invariant a+1 <= b && b <= M+1;
    {
      var c := M;
      while (c != a)
        invariant a <= c && c <= M;
      {
        assume X.Get(a,a) != 0;
        call X.Set(b, c, X.Get(b,c) - X.Get(b,a) / X.Get(a,a) * X.Get(a,c));
        c := c - 1;
      }
      b := b + 1;
    }
    a := a + 1;
    y := y * X.Get(a,a);
  }
  z := y;
}

class Matrix {
  ghost var Size: int;
  function method Get(i: int, j: int): int;
    requires 1 <= i && i <= Size;
    requires 1 <= j && j <= Size;
  method Set(i: int, j: int, x: int);
    requires 1 <= i && i <= Size;
    requires 1 <= j && j <= Size;
}
