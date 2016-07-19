class Number {
  ghost var Repr: set<object>;
  ghost var num: int;


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


  method Abs(a: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures num in {a, -a};
    ensures num >= 0;
  {
    if (a >= 0) {
      this.Init(a);
    } else {
      this.Init(-a);
    }
  }


  method Double(p: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures num == 2 * p;
  {
    this.Init(2 * p);
  }


  method Init(p: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures num == p;
  {
    this.num := p;

    // repr stuff
    this.Repr := {this};
  }


  method Min2(a: int, b: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures a < b ==> num == a;
    ensures a >= b ==> num == b;
  {
    if (a < b) {
      this.Init(a);
    } else {
      this.Init(b);
    }
  }


  method Min22(a: int, b: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures num in {a, b};
    ensures num <= a;
    ensures num <= b;
  {
    if (a <= b) {
      this.Init(a);
    } else {
      this.Init(b);
    }
  }


  method Min3(a: int, b: int, c: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures num in {a, b, c};
    ensures num <= a;
    ensures num <= b;
    ensures num <= c;
  {
    this.Min32(a, b, c);
  }


  method Min32(a: int, b: int, c: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures num in {a, b, c};
    ensures num <= a;
    ensures num <= b;
    ensures num <= c;
  {
    if (a <= b && a <= c) {
      this.Init(a);
    } else {
      if (c <= a && c <= b) {
        this.Init(c);
      } else {
        this.Init(b);
      }
    }
  }


  method Min4(a: int, b: int, c: int, d: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures num in {a, b, c, d};
    ensures num <= a;
    ensures num <= b;
    ensures num <= c;
    ensures num <= d;
  {
    if ((a <= b && a <= c) && a <= d) {
      this.Init(a);
    } else {
      if ((d <= a && d <= b) && d <= c) {
        this.Init(d);
      } else {
        if ((c <= a && c <= b) && c <= d) {
          this.Init(c);
        } else {
          this.Init(b);
        }
      }
    }
  }


  method MinSum(a: int, b: int, c: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures num in {a + b, a + c, b + c};
    ensures num <= a + b;
    ensures num <= b + c;
    ensures num <= a + c;
  {
    this.Min3(a + b, b + c, a + c);
  }


  method Sum(a: int, b: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures num == a + b;
  {
    this.Init(a + b);
  }

}


