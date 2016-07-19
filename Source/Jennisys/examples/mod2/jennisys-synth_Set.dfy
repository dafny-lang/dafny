class Set {
  ghost var Repr: set<object>;
  ghost var elems: set<int>;

  var root: SetNode;

  function Valid_repr(): bool
    reads *;
  {
    this in Repr &&
    null !in Repr &&
    (root != null ==> root in Repr && root.Repr <= Repr && this !in root.Repr)
  }

  function Valid_self(): bool
    reads *;
  {
    Valid_repr() &&
    (root == null ==> elems == {}) &&
    (root != null ==> elems == root.elems)
  }

  function Valid(): bool
    reads *;
  {
    this.Valid_self() &&
    (root != null ==> root.Valid())
  }


  method Double(p: int, q: int)
    modifies this;
    requires p != q;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {p, q};
  {
    var gensym80 := new SetNode;
    gensym80.Double(p, q);
    this.elems := {q, p};
    this.root := gensym80;

    // repr stuff
    this.Repr := {this} + this.root.Repr;
    // assert repr objects are valid (helps verification)
    assert gensym80.Valid();
  }


  method Empty()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {};
  {
    this.elems := {};
    this.root := null;

    // repr stuff
    this.Repr := {this};
  }


  method Singleton(t: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {t};
  {
    var gensym75 := new SetNode;
    gensym75.Init(t);
    this.elems := {t};
    this.root := gensym75;

    // repr stuff
    this.Repr := {this} + this.root.Repr;
    // assert repr objects are valid (helps verification)
    assert gensym75.Valid();
  }


  method SingletonZero()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {0};
  {
    this.Singleton(0);
  }


  method Sum(p: int, q: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {p + q};
  {
    this.Singleton(p + q);
  }

}

class SetNode {
  ghost var Repr: set<object>;
  ghost var elems: set<int>;

  var data: int;
  var left: SetNode;
  var right: SetNode;

  function Valid_repr(): bool
    reads *;
  {
    this in Repr &&
    null !in Repr &&
    (left != null ==> left in Repr && left.Repr <= Repr && this !in left.Repr) &&
    (right != null ==> right in Repr && right.Repr <= Repr && this !in right.Repr)
  }

  function Valid_self(): bool
    reads *;
  {
    Valid_repr() &&
    (elems == ({data} + (if left != null then left.elems else {})) + (if right != null then right.elems else {})) &&
    (left != null ==> (forall e :: e in left.elems ==> e < data)) &&
    (right != null ==> (forall e :: e in right.elems ==> e > data))
  }

  function Valid(): bool
    reads *;
    decreases Repr;
  {
    this.Valid_self() &&
    (left != null ==> left.Valid()) &&
    (right != null ==> right.Valid()) &&
    (left != null ==> left.Valid_self()) &&
    (right != null ==> right.Valid_self()) &&
    (left != null && left.left != null ==> left.left.Valid_self()) &&
    (left != null && left.right != null ==> left.right.Valid_self()) &&
    (right != null && right.left != null ==> right.left.Valid_self()) &&
    (right != null && right.right != null ==> right.right.Valid_self())
  }


  method Double(a: int, b: int)
    modifies this;
    requires a != b;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {a, b};
  {
    if (b > a) {
      this.DoubleBase(b, a);
    } else {
      var gensym88 := new SetNode;
      gensym88.Init(a);
      this.data := b;
      this.elems := {b, a};
      this.left := null;
      this.right := gensym88;

      // repr stuff
      this.Repr := {this} + this.right.Repr;
      // assert repr objects are valid (helps verification)
      assert gensym88.Valid();
    }
  }


  method DoubleBase(x: int, y: int)
    modifies this;
    requires x > y;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {x, y};
  {
    var gensym88 := new SetNode;
    gensym88.Init(x);
    this.data := y;
    this.elems := {y, x};
    this.left := null;
    this.right := gensym88;

    // repr stuff
    this.Repr := {this} + this.right.Repr;
    // assert repr objects are valid (helps verification)
    assert gensym88.Valid();
  }


  method Find(n: int) returns (ret: bool)
    requires Valid();
    ensures fresh(Repr - old(Repr));
    ensures Valid();
    ensures ret == (n in elems);
    decreases Repr;
  {
    if (this.left != null && this.right != null) {
      var x_9 := this.left.Find(n);
      var x_10 := this.right.Find(n);
      ret := (n == this.data || x_9) || x_10;
    } else {
      if (this.left != null && this.right == null) {
        var x_11 := this.left.Find(n);
        ret := n == this.data || x_11;
      } else {
        if (this.right != null && this.left == null) {
          var x_12 := this.right.Find(n);
          ret := n == this.data || x_12;
        } else {
          ret := n == this.data;
        }
      }
    }
  }


  method Init(x: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {x};
  {
    this.data := x;
    this.elems := {x};
    this.left := null;
    this.right := null;

    // repr stuff
    this.Repr := {this};
  }


  method Triple(x: int, y: int, z: int)
    modifies this;
    requires x != y;
    requires y != z;
    requires z != x;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {x, y, z};
  {
    if (z < x && y > x) {
      this.TripleBase(z, x, y);
    } else {
      if (x < y && z > y) {
        this.TripleBase(x, y, z);
      } else {
        if (x < z && y > z) {
          this.TripleBase(x, z, y);
        } else {
          if (y < z && x > z) {
            this.TripleBase(y, z, x);
          } else {
            if (z < y && x > y) {
              this.TripleBase(z, y, x);
            } else {
              var gensym82 := new SetNode;
              var gensym83 := new SetNode;
              gensym82.Init(y);
              gensym83.Init(z);
              this.data := x;
              this.elems := {y, x, z};
              this.left := gensym82;
              this.right := gensym83;

              // repr stuff
              this.Repr := ({this} + this.left.Repr) + this.right.Repr;
              // assert repr objects are valid (helps verification)
              assert gensym82.Valid() && gensym83.Valid();
            }
          }
        }
      }
    }
  }


  method TripleBase(x: int, y: int, z: int)
    modifies this;
    requires x < y;
    requires y < z;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {x, y, z};
  {
    var gensym89 := new SetNode;
    var gensym90 := new SetNode;
    gensym89.Init(z);
    gensym90.Init(x);
    this.data := y;
    this.elems := {x, y, z};
    this.left := gensym90;
    this.right := gensym89;

    // repr stuff
    this.Repr := ({this} + this.left.Repr) + this.right.Repr;
    // assert repr objects are valid (helps verification)
    assert gensym89.Valid() && gensym90.Valid();
  }

}


