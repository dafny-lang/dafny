class T {
  var x: int;

  use function F(y: int): int {
    2*y
  }

  method M(s: set<T>) {
    use F(4);
    use F(5);
    assert F(5) == 10;
    assert F(7) == 14;  // error (definition not engaged)
  }

  use function G(y: int): bool {
    0 <= y
  }

  method N(s: set<T>) {
    use G(4);
    use G(5);
    use G(-5);
    assert G(5);
    assert !G(-5);
    assert G(7);  // error (definition not engaged)
  }

  use function H(): int
    reads this;
  {
    x
  }

  method Q0()
    modifies this;
  {
    var t := x;
    use H();
    assert H() == t;

    x := x + 1;
    assert old(H()) == t;
  }

  method Q1()
    modifies this;
  {
    x := x + 1;
    use H();
    assert H() == old(H()) + 1;  // error: does not know what old(H()) is
  }

  method Q2()
    modifies this;
  {
    use H();
    x := x + 1;
    use H();
    assert H() == old(H()) + 1;
  }

  method Q3()
    modifies this;
  {
    x := x + 1;
    use H();
    use old(H());
    assert H() == old(H()) + 1;
  }
}
