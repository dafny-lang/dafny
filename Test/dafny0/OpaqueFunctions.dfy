module A {
  class C {
    var x: int;
    predicate Valid()
      reads this;
    {
      0 <= x
    }
    function Get(): int
      reads this;
    {
      x
    }
    constructor ()
      modifies this;
      ensures Valid();
    {
      x := 8;
    }
    method M()
      requires Valid();
    {
      assert Get() == x;
      assert x == 8;  // error
    }
  }
}
module A' refines A {
  class C {
    predicate Valid...
    {
      x == 8
    }
    method N()
      requires Valid();
    {
      assert Get() == x;
      assert x == 8;
    }
  }
}

module B {
  import X as A
  method Main() {
    var c := new X.C();
    c.M();  // fine
    c.x := c.x + 1;
    c.M();  // error, because Valid() is opaque
  }
  method L(c: X.C)
    requires c != null;
    modifies c;
  {
    assert c.Get() == c.x;  // error because Get() s opaque
    if * {
      assert c.Valid();  // error, because Valid() is opaque
    } else if * {
      c.x := 7;
      assert c.Valid();  // error, because Valid() is opaque
    } else {
      c.x := 8;
      assert c.Valid();  // error, because Valid() is opaque
    }
  }
}
module B_direct {
  import X as A'
  method Main() {
    var c := new X.C();
    c.M();  // fine
    c.x := c.x + 1;
    if * {
      assert c.Valid();  // error, because Valid() is opaque
    } else {
      c.M();  // error, because Valid() is opaque
    }
  }
  method L(c: X.C)
    requires c != null;
    modifies c;
  {
    assert c.Get() == c.x;  // error because Get() s opaque
    if * {
      assert c.Valid();  // error, because Valid() is opaque
    } else if * {
      c.x := 7;
      assert c.Valid();  // error, because Valid() is opaque
    } else {
      c.x := 8;
      assert c.Valid();  // error, because Valid() is opaque
    }
  }
}
module B' refines B {
  import X = A'  // this by itself produces no more error
  method Main'() {
    var c := new X.C();
    c.M();  // fine
    c.x := c.x + 1;
    if * {
      assert c.Valid();  // error, because Valid() is opaque
    } else {
      c.M();  // error, because Valid() is opaque
    }
  }
  method L'(c: X.C)
    requires c != null;
    modifies c;
  {
    assert c.Get() == c.x;  // error because Get() s opaque
    if * {
      assert c.Valid();  // error, because Valid() is opaque
    } else if * {
      c.x := 7;
      assert c.Valid();  // error, because Valid() is opaque
    } else {
      c.x := 8;
      assert c.Valid();  // error, because Valid() is opaque
    }
  }
}

