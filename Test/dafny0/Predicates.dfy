module A {
  class C {
    var x: int;
    predicate P()
      reads this;
    {
      x < 100
    }
    method M()
      modifies this;
      ensures P();
    {
      x := 28;
    }
    method N()
      modifies this;
      ensures P();
    {
      x := -28;
    }
  }
}

module B refines A {
  class C {
    predicate P()
    {
      0 <= x
    }
  }
}
