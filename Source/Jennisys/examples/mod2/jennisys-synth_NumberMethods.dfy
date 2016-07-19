class NumberMethods {
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
    if (-a >= 0) {
      ret := -a;
    } else {
      ret := a;
    }
  }


  method Double(p: int) returns (ret: int)
    requires Valid();
    ensures fresh(Repr - old(Repr));
    ensures Valid();
    ensures ret == 2 * p;
  {
    ret := 2 * p;
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


  method Min22(a: int, b: int) returns (ret: int)
    requires Valid();
    ensures fresh(Repr - old(Repr));
    ensures Valid();
    ensures ret in {a, b};
    ensures ret <= a;
    ensures ret <= b;
  {
    if (a <= b) {
      ret := a;
    } else {
      ret := b;
    }
  }


  method Min3(a: int, b: int, c: int) returns (ret: int)
    requires Valid();
    ensures fresh(Repr - old(Repr));
    ensures Valid();
    ensures ret in {a, b, c};
    ensures ret <= a;
    ensures ret <= b;
    ensures ret <= c;
  {
    ret := this.Min32(a, b, c);
  }


  method Min32(a: int, b: int, c: int) returns (ret: int)
    requires Valid();
    ensures fresh(Repr - old(Repr));
    ensures Valid();
    ensures ret in {a, b, c};
    ensures ret <= a;
    ensures ret <= b;
    ensures ret <= c;
  {
    if (a <= b && a <= c) {
      ret := a;
    } else {
      if (c <= a && c <= b) {
        ret := c;
      } else {
        ret := b;
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
      if ((d <= a && d <= b) && d <= c) {
        ret := d;
      } else {
        if ((c <= a && c <= b) && c <= d) {
          ret := c;
        } else {
          ret := b;
        }
      }
    }
  }


  method MinSum(a: int, b: int, c: int) returns (ret: int)
    requires Valid();
    ensures fresh(Repr - old(Repr));
    ensures Valid();
    ensures ret in {a + b, a + c, b + c};
    ensures ret <= a + b;
    ensures ret <= b + c;
    ensures ret <= a + c;
  {
    ret := this.Min3(a + b, b + c, a + c);
  }


  method Sum(a: int, b: int) returns (ret: int)
    requires Valid();
    ensures fresh(Repr - old(Repr));
    ensures Valid();
    ensures ret == a + b;
  {
    ret := a + b;
  }

}


