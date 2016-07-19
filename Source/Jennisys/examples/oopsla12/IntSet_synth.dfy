class IntSet {
  ghost var Repr: set<object>;
  ghost var elems: set<int>;

  var data: int;
  var left: IntSet;
  var right: IntSet;

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
    (right != null ==> (forall e :: e in right.elems ==> data < e))
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


  method Dupleton(x: int, y: int)
    modifies this;
    requires x != y;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {x, y};
  {
    if (x < y) {
      var gensym73 := new IntSet;
      this.data := x;
      this.elems := {x, y};
      this.left := null;
      this.right := gensym73;
      gensym73.data := y;
      gensym73.elems := {y};
      gensym73.left := null;
      gensym73.right := null;

      // repr stuff
      gensym73.Repr := {gensym73};
      this.Repr := {this} + {gensym73};
      // assert repr objects are valid (helps verification)
      assert gensym73.Valid();
    } else {
      var gensym73 := new IntSet;
      this.data := y;
      this.elems := {y, x};
      this.left := null;
      this.right := gensym73;
      gensym73.data := x;
      gensym73.elems := {x};
      gensym73.left := null;
      gensym73.right := null;

      // repr stuff
      gensym73.Repr := {gensym73};
      this.Repr := {this} + {gensym73};
      // assert repr objects are valid (helps verification)
      assert gensym73.Valid();
    }
  }


  method Find(x: int) returns (ret: bool)
    requires Valid();
    ensures fresh(Repr - old(Repr));
    ensures Valid();
    ensures ret == (x in elems);
    decreases Repr;
  {
    if (this.left != null && this.right != null) {
      var x_13 := this.left.Find(x);
      var x_14 := this.right.Find(x);
      ret := (x == this.data || x_13) || x_14;
    } else {
      if (this.left != null) {
        var x_15 := this.left.Find(x);
        ret := x == this.data || x_15;
      } else {
        if (this.right != null) {
          var x_16 := this.right.Find(x);
          ret := x == this.data || x_16;
        } else {
          ret := x == this.data;
        }
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

}


