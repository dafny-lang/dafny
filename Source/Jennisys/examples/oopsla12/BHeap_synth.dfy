class BHeap {
  ghost var Repr: set<object>;
  ghost var elems: set<int>;

  var data: int;
  var left: BHeap;
  var right: BHeap;

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
    (right != null ==> (forall e :: e in right.elems ==> e < data)) &&
    (left == null ==> right == null) &&
    (left != null && right == null ==> left.elems == {left.data})
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


  method Dupleton(a: int, b: int)
    modifies this;
    requires a != b;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {a, b};
  {
    if (b < a) {
      var gensym71 := new BHeap;
      var gensym73 := new BHeap;
      this.data := a;
      this.elems := {b, a};
      this.left := gensym73;
      this.right := gensym71;
      gensym71.data := b;
      gensym71.elems := {b};
      gensym71.left := null;
      gensym71.right := null;
      gensym73.data := b;
      gensym73.elems := {b};
      gensym73.left := null;
      gensym73.right := null;

      // repr stuff
      gensym71.Repr := {gensym71};
      gensym73.Repr := {gensym73};
      this.Repr := ({this} + {gensym73}) + {gensym71};
      // assert repr objects are valid (helps verification)
      assert gensym71.Valid() && gensym73.Valid();
    } else {
      var gensym71 := new BHeap;
      var gensym73 := new BHeap;
      this.data := b;
      this.elems := {a, b};
      this.left := gensym73;
      this.right := gensym71;
      gensym71.data := a;
      gensym71.elems := {a};
      gensym71.left := null;
      gensym71.right := null;
      gensym73.data := a;
      gensym73.elems := {a};
      gensym73.left := null;
      gensym73.right := null;

      // repr stuff
      gensym71.Repr := {gensym71};
      gensym73.Repr := {gensym73};
      this.Repr := ({this} + {gensym73}) + {gensym71};
      // assert repr objects are valid (helps verification)
      assert gensym71.Valid() && gensym73.Valid();
    }
  }


  method Find(n: int) returns (ret: bool)
    requires Valid();
    ensures fresh(Repr - old(Repr));
    ensures Valid();
    ensures ret == (n in elems);
    decreases Repr;
  {
    if (this.left == null) {
      ret := n == this.data;
    } else {
      if (this.right != null) {
        var x_10 := this.left.Find(n);
        var x_11 := this.right.Find(n);
        ret := (n == this.data || x_10) || x_11;
      } else {
        var x_12 := this.left.Find(n);
        ret := n == this.data || x_12;
      }
    }
  }


  method Singleton(x: int)
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


  method Tripleton(x: int, y: int, z: int)
    modifies this;
    requires x != y;
    requires y != z;
    requires z != x;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {x, y, z};
  {
    if (z < y && x < y) {
      var gensym75 := new BHeap;
      var gensym77 := new BHeap;
      this.data := y;
      this.elems := {z, x, y};
      this.left := gensym77;
      this.right := gensym75;
      gensym75.data := x;
      gensym75.elems := {x};
      gensym75.left := null;
      gensym75.right := null;
      gensym77.data := z;
      gensym77.elems := {z};
      gensym77.left := null;
      gensym77.right := null;

      // repr stuff
      gensym75.Repr := {gensym75};
      gensym77.Repr := {gensym77};
      this.Repr := ({this} + {gensym77}) + {gensym75};
      // assert repr objects are valid (helps verification)
      assert gensym75.Valid() && gensym77.Valid();
    } else {
      if (x < z) {
        var gensym75 := new BHeap;
        var gensym77 := new BHeap;
        this.data := z;
        this.elems := {x, y, z};
        this.left := gensym77;
        this.right := gensym75;
        gensym75.data := x;
        gensym75.elems := {x};
        gensym75.left := null;
        gensym75.right := null;
        gensym77.data := y;
        gensym77.elems := {y};
        gensym77.left := null;
        gensym77.right := null;

        // repr stuff
        gensym75.Repr := {gensym75};
        gensym77.Repr := {gensym77};
        this.Repr := ({this} + {gensym77}) + {gensym75};
        // assert repr objects are valid (helps verification)
        assert gensym75.Valid() && gensym77.Valid();
      } else {
        var gensym75 := new BHeap;
        var gensym77 := new BHeap;
        this.data := x;
        this.elems := {z, y, x};
        this.left := gensym77;
        this.right := gensym75;
        gensym75.data := y;
        gensym75.elems := {y};
        gensym75.left := null;
        gensym75.right := null;
        gensym77.data := z;
        gensym77.elems := {z};
        gensym77.left := null;
        gensym77.right := null;

        // repr stuff
        gensym75.Repr := {gensym75};
        gensym77.Repr := {gensym77};
        this.Repr := ({this} + {gensym77}) + {gensym75};
        // assert repr objects are valid (helps verification)
        assert gensym75.Valid() && gensym77.Valid();
      }
    }
  }

}


