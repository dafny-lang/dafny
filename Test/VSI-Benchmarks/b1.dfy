// Spec# and Boogie and Chalice:  The program will be
// the same, except that these languages do not check
// for any kind of termination.  Also, in Spec#, there
// is an issue of potential overflows.

// Benchmark1

method Add(x: int, y: int) returns (r: int)
  ensures r == x+y;
{
  r := x;
  if (y < 0) {
    var n := y;
    while (n != 0)
      invariant r == x+y-n && 0 <= -n;
    {
      r := r - 1;
      n := n + 1;
    }
  } else {
    var n := y;
    while (n != 0)
      invariant r == x+y-n && 0 <= n;
    {
      r := r + 1;
      n := n - 1;
    }
  }
}

method Mul(x: int, y: int) returns (r: int)
  ensures r == x*y;
  decreases x < 0, x;
{
  if (x == 0) {
    r := 0;
  } else if (x < 0) {
    call r := Mul(-x, y);
    r := -r;
  } else {
    call r := Mul(x-1, y);
    call r := Add(r, y);
  }
}

// ---------------------------

method Main() {
  call TestAdd(3, 180);
  call TestAdd(3, -180);
  call TestAdd(0, 1);

  call TestMul(3, 180);
  call TestMul(3, -180);
  call TestMul(180, 3);
  call TestMul(-180, 3);
  call TestMul(0, 1);
  call TestMul(1, 0);
}

method TestAdd(x: int, y: int) {
  print x, " + ", y, " = ";
  call z := Add(x, y);
  print z, "\n";
}

method TestMul(x: int, y: int) {
  print x, " * ", y, " = ";
  call z := Mul(x, y);
  print z, "\n";
}
