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
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {p, q};
  {
    var gensym67 := new SetNode;
    gensym67.Double(p, q);
    this.elems := {p, q};
    this.root := gensym67;
    // repr stuff
    this.Repr := {this} + this.root.Repr;
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
    var gensym67 := new SetNode;
    gensym67.Init(t);
    this.elems := {t};
    this.root := gensym67;
    // repr stuff
    this.Repr := {this} + this.root.Repr;
  }


  method Sum(p: int, q: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {p + q};
  {
    var gensym69 := new SetNode;
    gensym69.Init(p + q);
    this.elems := {p + q};
    this.root := gensym69;
    // repr stuff
    this.Repr := {this} + this.root.Repr;
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
  {
    this.Valid_self() &&
    (left != null ==> left.Valid_self()) &&
    (right != null ==> right.Valid_self()) &&
    (left != null && left.left != null ==> left.left.Valid_self()) &&
    (left != null && left.right != null ==> left.right.Valid_self()) &&
    (right != null && right.left != null ==> right.left.Valid_self()) &&
    (right != null && right.right != null ==> right.right.Valid_self())
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
    if (x < y && z > y) {
      var gensym80 := new SetNode;
      var gensym81 := new SetNode;
      gensym80.Init(z);
      gensym81.Init(x);
      this.data := y;
      this.elems := {x, y, z};
      this.left := gensym81;
      this.right := gensym80;
      // repr stuff
      this.Repr := ({this} + this.left.Repr) + this.right.Repr;
    } else {
      if (z < x && y > x) {
        var gensym80 := new SetNode;
        var gensym81 := new SetNode;
        gensym80.Init(y);
        gensym81.Init(z);
        this.data := x;
        this.elems := {x, y, z};
        this.left := gensym81;
        this.right := gensym80;
        // repr stuff
        this.Repr := ({this} + this.left.Repr) + this.right.Repr;
      } else {
        if (x < z && y > z) {
          var gensym80 := new SetNode;
          var gensym81 := new SetNode;
          gensym80.Init(y);
          gensym81.Init(x);
          this.data := z;
          this.elems := {x, y, z};
          this.left := gensym81;
          this.right := gensym80;
          // repr stuff
          this.Repr := ({this} + this.left.Repr) + this.right.Repr;
        } else {
          if (z < y && x > y) {
            var gensym80 := new SetNode;
            var gensym81 := new SetNode;
            gensym80.Init(x);
            gensym81.Init(z);
            this.data := y;
            this.elems := {x, y, z};
            this.left := gensym81;
            this.right := gensym80;
            // repr stuff
            this.Repr := ({this} + this.left.Repr) + this.right.Repr;
          } else {
            if (y < z && x > z) {
              var gensym80 := new SetNode;
              var gensym81 := new SetNode;
              gensym80.Init(x);
              gensym81.Init(y);
              this.data := z;
              this.elems := {x, y, z};
              this.left := gensym81;
              this.right := gensym80;
              // repr stuff
              this.Repr := ({this} + this.left.Repr) + this.right.Repr;
            } else {
              var gensym80 := new SetNode;
              var gensym81 := new SetNode;
              gensym80.Init(z);
              gensym81.Init(y);
              this.data := x;
              this.elems := {x, y, z};
              this.left := gensym81;
              this.right := gensym80;
              // repr stuff
              this.Repr := ({this} + this.left.Repr) + this.right.Repr;
            }
          }
        }
      }
    }
  }


  method Double(x: int, y: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {x, y};
  {
    if (y > x) {
      var gensym77 := new SetNode;
      gensym77.Init(y);
      this.data := x;
      this.elems := {x, y};
      this.left := null;
      this.right := gensym77;
      // repr stuff
      this.Repr := {this} + this.right.Repr;
    } else {
      if (x > y) {
        var gensym77 := new SetNode;
        gensym77.Init(x);
        this.data := y;
        this.elems := {x, y};
        this.left := null;
        this.right := gensym77;
        // repr stuff
        this.Repr := {this} + this.right.Repr;
      } else {
        this.data := y;
        this.elems := {x, y};
        this.left := null;
        this.right := null;
        // repr stuff
        this.Repr := {this};
      }
    }
  }

}


