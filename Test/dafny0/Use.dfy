class T {
  var x: int;

  function F(y: int): int
    decreases false;
  {
    2*y + (if 1 < 0 then FEntry(y) else 0)
  }
  function FEntry(y: int): int decreases true; { F(y) }

  method M(s: set<T>) {
    use F(4);
    use F(5);
    assert F(5) == 10;
    assert F(7) == 14;
    assert F(72) == 14;  // error (just plain wrong)
  }

  function FF(y: int): int
  {
    FEntry(y)
  }

  method MM() {
    assert F(5) == 10;
    assert FF(6) == 12;  // error (definition of F not engaged)

    assert F(7) == 14;
    assert FF(7) == 14;  // now the inner definition of F has already been engaged

    use F(8);
    assert FF(8) == 16;  // same here

    use FF(9);
    assert FF(9) == 18;  // error (definition of F not engaged; the use of FF does not help)
  }

  function G(y: int): bool decreases false;
  {
    0 <= y || (1 < 0 && GG(y))
  }
  unlimited function GG(y: int): bool decreases true;
  {
    G(y)
  }

  method N(s: set<T>) {
    use G(4);
    use G(5);
    use G(-5);
    assert GG(5);
    assert !GG(-5);
    assert GG(7);  // fine (the assert expands GG to G, then the definition of G kicks in)
    assert !GG(-7);  // error (the negation disables the expansion of GG in the assert)
  }

  function H(): int
    reads this; decreases false;
  {
    x + (if 1 < 0 then HH() else 0)
  }
  unlimited function HH(): int
    reads this; decreases true;
  {
    H()
  }

  method Q0()
    modifies this;
  {
    var t := x;
    use H();
    assert HH() == t;

    x := x + 1;
    assert old(HH()) == t;
  }

  method Q1()
    modifies this;
  {
    x := x + 1;
    use H();
    assert HH() == old(HH()) + 1;  // error: does not know what old(H()) is
  }

  method Q2()
    modifies this;
  {
    use H();
    x := x + 1;
    use H();
    assert HH() == old(HH()) + 1;
  }

  method Q3()
    modifies this;
  {
    x := x + 1;
    use H();
    use old(H());
    assert HH() == old(HH()) + 1;
  }

  method Q4(other: T)
    requires other != null && other != this;
    modifies other;
  {
    other.x := other.x + 1;
    assert HH() == old(HH());  // frame axiom for H still works
  }

  method Q5(other: T)
    requires other != null && other != this;
    modifies this;
  {
    x := x + 1;
    assert other.HH() == old(other.HH());  // frame axiom for H still works
  }

  method Q6(other: T)
    requires other != null;
    modifies this;
  {
    x := x + 1;
    assert other.HH() == old(other.HH());  // error: 'other' may equal 'this', in which
                                           // case nothing is known about how H() changed
  }

  function K(): bool
    reads this; decreases false;
  {
    x <= 100 || (1 < 0 && KK())
  }
  unlimited function KK(): bool
    reads this; decreases true;
  {
    K()
  }

  method R0()
    requires KK();
    modifies this;
  {
    x := x - 1;
    assert KK();  // error (does not know exact definition of K from the initial state)
  }

  method R1()
    requires KK();
    modifies this;
  {
    use K();  // KK in the precondition and KK's definition give K#limited, which this use expands
    x := x - 1;
    assert KK();  // the assert expands KK to K, definition of K expands K
  }

  method R2()
    requires KK();
    modifies this;
  {
    x := x - 1;
    use K();
    assert KK();  // error (does not know exact definition of K in the pre-state)
  }

  method R3()
    requires KK();
    modifies this;
  {
    use K();
    x := x - 1;
    use K();
    assert KK();  // thar it is
  }
}

class Recursive {
  function Gauss(n: int): int
    requires 0 <= n;
    decreases n;
  {
    if n == 0 then 0 else Gauss(n-1) + n
  }

  ghost method G(n: int)
    requires 0 <= n;
    ensures Gauss(n) == (n+1)*n / 2;
  {
    var k := 0;
    while (k < n)
      invariant k <= n;
      invariant Gauss(k) == (k+1)*k / 2;
    {
      k := k + 1;
    }
  }

  function Fib(n: int): int
    requires 0 <= n;
    decreases n;
  {
    if n < 2 then n else Fib(n-2) + Fib(n-1)
  }

  method F0()
  {
    assert Fib(2) == 1;  // error (does not know about Fib for the recursive calls)
  }

  method F1()
  {
    assert Fib(0) == 0;
    assert Fib(1) == 1;
    assert Fib(2) == 1;  // now it knows
  }

  method F2()
  {
    assert Fib(0) == 0;
    use Fib(1);
    assert Fib(2) == 1;  // now it knows, too
  }
}
