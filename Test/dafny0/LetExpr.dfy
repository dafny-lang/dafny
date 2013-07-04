method M0(n: int)
  requires var f := 100; n < f; requires var t, f := true, false; (t && f) || n < 100;
{
  assert n < 200;
  assert 0 <= n;  // error
}

method M1()
{
  assert var f := 54; var g := f + 1; g == 55;
}

method M2()
{
  assert var f := 54; var f := f + 1; f == 55;
}

function method Fib(n: nat): nat
{
  if n < 2 then n else Fib(n-1) + Fib(n-2)
}

method M3(a: array<int>) returns (r: int)
  requires a != null && forall i :: 0 <= i < a.Length ==> a[i] == 6;
  ensures (r + var t := r; t*2) == 3*r;
{
  assert Fib(2) + Fib(4) == Fib(0) + Fib(1) + Fib(2) + Fib(3);

  {
    var x,y := Fib(8), Fib(11);
    assume x == 21;
    assert Fib(7) == 3 ==> Fib(9) == 24;
    assume Fib(1000) == 1000;
    assume Fib(9) - Fib(8) == 13;
    assert Fib(9) <= Fib(10);
    assert y == 89;
  }

  assert Fib(1000) == 1000;  // does it still know this?

  forall i | 0 <= i < a.Length ensures true; {
    var j := i+1;
    assert j < a.Length ==> a[i] == a[j];
  }
}

// M4 is pretty much the same as M3, except with things rolled into expressions.
method M4(a: array<int>) returns (r: int)
  requires a != null && forall i :: 0 <= i < a.Length ==> a[i] == 6;
  ensures (r + var t := r; t*2) == 3*r;
{
  assert Fib(2) + Fib(4) == Fib(0) + Fib(1) + Fib(2) + Fib(3);
  assert
    var x,y := Fib(8), Fib(11);
    assume x == 21;
    assert Fib(7) == 3 ==> Fib(9) == 24;
    assume Fib(1000) == 1000;
    assume Fib(9) - Fib(8) == 13;
    assert Fib(9) <= Fib(10);
    y == 89;
  assert Fib(1000) == 1000;  // still known, because the assume was on the path here
  assert forall i :: 0 <= i < a.Length ==> var j := i+1; j < a.Length ==> a[i] == a[j];
}

var index: int;
method P(a: array<int>) returns (b: bool, ii: int)
  requires a != null && exists k :: 0 <= k < a.Length && a[k] == 19;
  modifies this, a;
  ensures ii == index;
  // The following uses a variable with a non-old definition inside an old expression:
  ensures 0 <= index < a.Length && old(a[ii]) == 19;
  ensures 0 <= index < a.Length && var newIndex := index; old(a[newIndex]) == 19;
  // The following places both the variable and the body inside an old:
  ensures b ==> old(var oldIndex := index; 0 <= oldIndex < a.Length && a[oldIndex] == 17);
  // Here, the definition of the variable is old, and it's used both inside and
  // inside an old expression:
  ensures var oi := old(index); oi == index ==> a[oi] == 21 && old(a[oi]) == 19;
{
  b := 0 <= index < a.Length && a[index] == 17;
  var i, j := 0, -1;
  while (i < a.Length)
    invariant 0 <= i <= a.Length;
    invariant forall k :: 0 <= k < i ==> a[k] == 21;
    invariant forall k :: i <= k < a.Length ==> a[k] == old(a[k]);
    invariant (0 <= j < i && old(a[j]) == 19) ||
              (j == -1 && exists k :: i <= k < a.Length && a[k] == 19);
  {
    if (a[i] == 19) { j := i; }
    i, a[i] := i + 1, 21;
  }
  index := j;
  ii := index;
}

method PMain(a: array<int>)
  requires a != null && exists k :: 0 <= k < a.Length && a[k] == 19;
  modifies this, a;
{
  var s := a[..];
  var b17, ii := P(a);
  assert s == old(a[..]);
  assert s[index] == 19;
  if (*) {
    assert a[index] == 19;  // error (a can have changed in P)
  } else {
    assert b17 ==> 0 <= old(index) < a.Length && old(a[index]) == 17;
    assert index == old(index) ==> a[index] == 21 && old(a[index]) == 19;
  }
}

// ---------- lemmas ----------

method Theorem0(n: int)
  requires 1 <= n;
  ensures 1 <= Fib(n);
{
  if (n < 3) {
  } else {
    Theorem0(n-2);
    Theorem0(n-1);
  }
}

ghost method Theorem1(n: int)
  requires 1 <= n;
  ensures 1 <= Fib(n);
{
  // in a ghost method, the induction tactic takes care of it
}

function Theorem2(n: int): int
  requires 1 <= n;
  ensures 1 <= Fib(n);
{
  if n < 3 then 5 else
    var x := Theorem2(n-2);
    var y := Theorem2(n-1);
    x + y
}

function Theorem3(n: int): int
  requires 1 <= n;
  ensures 1 <= Fib(n);
{
  if n < 3 then 5 else
    var x := Theorem3(n-2);
    var y := Theorem3(n-1);
    5
}

// ----- tricky substitution issues in the implementation -----

class TrickySubstitution {
  function F0(x: int): int
    ensures F0(x) == x;
  {
    var g :| x == g;
    g
  }

  function F1(x: int): int
    ensures F1(x) == x;
  {
    var f := x;
    var g :| f == g;
    g
  }

  function F2(x: int): int
    ensures F2(x) == x;
  {
    var f, g :| f == x && f == g;
    g
  }

  function F3(x: int): int
    ensures F3(x) == x;
  {
    var f :| f == x;
    var g :| f == g;
    g
  }

  var v: int;
  var w: int;

  function F4(x: int): int
    requires this.v + x == 3 && this.w == 2;
    reads this;
    ensures F4(x) == 5;
  {
    var f := this.v + x;  // 3
    var g :| f + this.w == g;  // 5
    g
  }

  method M(x: int)
    requires this.v + x == 3 && this.w == 2;
    modifies this;
  {
    this.v := this.v + 1;
    this.w := this.w + 10;
    assert 6 ==
      var f := this.v + x;  // 4
      var g :| old(f + this.w) == g;  // 6
      g;
  }

  method N() returns (ghost r: int, ghost s: int)
    requires w == 12;
    modifies this;
    ensures r == 12 == s && w == 13;
  {
    w := w + 1;
    r := var y :| y == old(w); y;
    s := old(var y :| y == w; y);
  }
}
