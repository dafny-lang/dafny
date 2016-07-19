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

  method Double(p: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures num == 2 * p;
  {
    this.num := 2 * p;
    // repr stuff
    this.Repr := {this};
  }

  method Sum(a: int, b: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures num == a + b;
  {
    this.num := a + b;
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
    if (a >= b ==> a == b) {
      this.num := a;
      // repr stuff
      this.Repr := {this};
    } else {
      this.num := b;
      // repr stuff
      this.Repr := {this};
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
      this.num := a;
      // repr stuff
      this.Repr := {this};
    } else {
      this.num := b;
      // repr stuff
      this.Repr := {this};
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
    if (a <= b && a <= c) {
      this.num := a;
      // repr stuff
      this.Repr := {this};
    } else {
      if (c <= a && c <= b) {
        this.num := c;
        // repr stuff
        this.Repr := {this};
      } else {
        this.num := b;
        // repr stuff
        this.Repr := {this};
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
    if (a + b <= b + c && a + b <= a + c) {
      this.num := a + b;
      // repr stuff
      this.Repr := {this};
    } else {
      if (a + c <= a + b && a + c <= b + c) {
        this.num := a + c;
        // repr stuff
        this.Repr := {this};
      } else {
        this.num := b + c;
        // repr stuff
        this.Repr := {this};
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
    if (a <= b && (a <= c && a <= d)) {
      this.num := a;
      // repr stuff
      this.Repr := {this};
    } else {
      if (d <= a && (d <= b && d <= c)) {
        this.num := d;
        // repr stuff
        this.Repr := {this};
      } else {
        if (c <= a && (c <= b && c <= d)) {
          this.num := c;
          // repr stuff
          this.Repr := {this};
        } else {
          this.num := b;
          // repr stuff
          this.Repr := {this};
        }
      }
    }
  }

  method Abs(a: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures a < 0 ==> num == -a;
    ensures a >= 0 ==> num == a;
  {
    if (!(a >= 0)) {
      this.num := -a;
      // repr stuff
      this.Repr := {this};
    } else {
      this.num := a;
      // repr stuff
      this.Repr := {this};
    }
  }

}


