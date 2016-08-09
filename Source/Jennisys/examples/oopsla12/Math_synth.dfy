class Math {
  ghost var Repr: set<object>;


  function Valid_repr(): bool
    reads *;
  {
    this in Repr &&
    null !in Repr
  }

  function Valid_self(): bool
    reads *;
  {
    Valid_repr() &&
    true
  }

  function Valid(): bool
    reads *;
  {
    this.Valid_self() &&
    true
  }


  method Abs(a: int) returns (ret: int)
    requires Valid();
    ensures fresh(Repr - old(Repr));
    ensures Valid();
    ensures ret in {a, -a};
    ensures ret >= 0;
  {
    if (a >= 0) {
      ret := a;
    } else {
      ret := -a;
    }
  }


  method Min2(a: int, b: int) returns (ret: int)
    requires Valid();
    ensures fresh(Repr - old(Repr));
    ensures Valid();
    ensures a < b ==> ret == a;
    ensures a >= b ==> ret == b;
  {
    if (a < b) {
      ret := a;
    } else {
      ret := b;
    }
  }


  method Min3Sum(a: int, b: int, c: int) returns (ret: int)
    requires Valid();
    ensures fresh(Repr - old(Repr));
    ensures Valid();
    ensures ret in {a + b, a + c, b + c};
    ensures ret <= a + b;
    ensures ret <= a + c;
    ensures ret <= b + c;
  {
    if (a + b <= a + c && a + b <= b + c) {
      ret := a + b;
    } else {
      if (b + c <= a + c) {
        ret := b + c;
      } else {
        ret := a + c;
      }
    }
  }


  method Min4(a: int, b: int, c: int, d: int) returns (ret: int)
    requires Valid();
    ensures fresh(Repr - old(Repr));
    ensures Valid();
    ensures ret in {a, b, c, d};
    ensures ret <= a;
    ensures ret <= b;
    ensures ret <= c;
    ensures ret <= d;
  {
    if ((a <= b && a <= c) && a <= d) {
      ret := a;
    } else {
      if (d <= b && d <= c) {
        ret := d;
      } else {
        if (c <= b) {
          ret := c;
        } else {
          ret := b;
        }
      }
    }
  }

}


