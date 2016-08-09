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
    var gensym66 := new SetNode;
    gensym66.data := t;
    gensym66.elems := {t};
    gensym66.left := null;
    gensym66.right := null;
    this.elems := {t};
    this.root := gensym66;
    // repr stuff
    gensym66.Repr := {gensym66};
    this.Repr := {this} + this.root.Repr;
  }

  method Sum(p: int, q: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {p + q};
  {
    var gensym68 := new SetNode;
    gensym68.data := p + q;
    gensym68.elems := {p + q};
    gensym68.left := null;
    gensym68.right := null;
    this.elems := {p + q};
    this.root := gensym68;
    // repr stuff
    gensym68.Repr := {gensym68};
    this.Repr := {this} + this.root.Repr;
  }

  method Double(p: int, q: int)
    modifies this;
    requires p != q;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {p, q};
  {
    if (q < p) {
      var gensym71 := new SetNode;
      var gensym75 := new SetNode;
      gensym71.data := p;
      gensym71.elems := {p, q};
      gensym71.left := gensym75;
      gensym71.right := null;
      gensym75.data := q;
      gensym75.elems := {q};
      gensym75.left := null;
      gensym75.right := null;
      this.elems := {p, q};
      this.root := gensym71;
      // repr stuff
      gensym75.Repr := {gensym75};
      gensym71.Repr := {gensym71} + gensym71.left.Repr;
      this.Repr := {this} + this.root.Repr;
    } else {
      var gensym71 := new SetNode;
      var gensym75 := new SetNode;
      gensym71.data := q;
      gensym71.elems := {p, q};
      gensym71.left := gensym75;
      gensym71.right := null;
      gensym75.data := p;
      gensym75.elems := {p};
      gensym75.left := null;
      gensym75.right := null;
      this.elems := {p, q};
      this.root := gensym71;
      // repr stuff
      gensym75.Repr := {gensym75};
      gensym71.Repr := {gensym71} + gensym71.left.Repr;
      this.Repr := {this} + this.root.Repr;
    }
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
    (left != null ==> left.Valid_self() && (left.left != null ==> left.left.Valid_self())) &&
    (right != null ==> right.Valid_self() && (right.right != null ==> right.right.Valid_self()))
  }

  method Init(t: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {t};
  {
    this.data := t;
    this.elems := {t};
    this.left := null;
    this.right := null;
    // repr stuff
    this.Repr := {this};
  }

  method Double(p: int, q: int)
    modifies this;
    requires p != q;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {p, q};
  {
    if (q > p) {
      var gensym79 := new SetNode;
      gensym79.data := q;
      gensym79.elems := {q};
      gensym79.left := null;
      gensym79.right := null;
      this.data := p;
      this.elems := {p, q};
      this.left := null;
      this.right := gensym79;
      // repr stuff
      gensym79.Repr := {gensym79};
      this.Repr := {this} + this.right.Repr;
    } else {
      var gensym79 := new SetNode;
      gensym79.data := p;
      gensym79.elems := {p};
      gensym79.left := null;
      gensym79.right := null;
      this.data := q;
      this.elems := {p, q};
      this.left := null;
      this.right := gensym79;
      // repr stuff
      gensym79.Repr := {gensym79};
      this.Repr := {this} + this.right.Repr;
    }
  }

  method Triple(p: int, q: int, r: int)
    modifies this;
    requires p != q;
    requires q != r;
    requires r != p;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {p, q, r};
  {
    if (p < q && r > q) {
      var gensym83 := new SetNode;
      var gensym84 := new SetNode;
      gensym83.data := r;
      gensym83.elems := {r};
      gensym83.left := null;
      gensym83.right := null;
      gensym84.data := p;
      gensym84.elems := {p};
      gensym84.left := null;
      gensym84.right := null;
      this.data := q;
      this.elems := {p, q, r};
      this.left := gensym84;
      this.right := gensym83;
      // repr stuff
      gensym83.Repr := {gensym83};
      gensym84.Repr := {gensym84};
      this.Repr := ({this} + this.left.Repr) + this.right.Repr;
    } else {
      if (p < r && q > r) {
        var gensym85 := new SetNode;
        var gensym86 := new SetNode;
        gensym85.data := q;
        gensym85.elems := {q};
        gensym85.left := null;
        gensym85.right := null;
        gensym86.data := p;
        gensym86.elems := {p};
        gensym86.left := null;
        gensym86.right := null;
        this.data := r;
        this.elems := {p, q, r};
        this.left := gensym86;
        this.right := gensym85;
        // repr stuff
        gensym85.Repr := {gensym85};
        gensym86.Repr := {gensym86};
        this.Repr := ({this} + this.left.Repr) + this.right.Repr;
      } else {
        if (r < p && q > p) {
          var gensym84 := new SetNode;
          var gensym85 := new SetNode;
          gensym84.data := q;
          gensym84.elems := {q};
          gensym84.left := null;
          gensym84.right := null;
          gensym85.data := r;
          gensym85.elems := {r};
          gensym85.left := null;
          gensym85.right := null;
          this.data := p;
          this.elems := {p, q, r};
          this.left := gensym85;
          this.right := gensym84;
          // repr stuff
          gensym84.Repr := {gensym84};
          gensym85.Repr := {gensym85};
          this.Repr := ({this} + this.left.Repr) + this.right.Repr;
        } else {
          if (q < p && r > p) {
            var gensym82 := new SetNode;
            var gensym83 := new SetNode;
            gensym82.data := r;
            gensym82.elems := {r};
            gensym82.left := null;
            gensym82.right := null;
            gensym83.data := q;
            gensym83.elems := {q};
            gensym83.left := null;
            gensym83.right := null;
            this.data := p;
            this.elems := {p, q, r};
            this.left := gensym83;
            this.right := gensym82;
            // repr stuff
            gensym82.Repr := {gensym82};
            gensym83.Repr := {gensym83};
            this.Repr := ({this} + this.left.Repr) + this.right.Repr;
          } else {
            if (q < r && p > r) {
              var gensym85 := new SetNode;
              var gensym86 := new SetNode;
              gensym85.data := p;
              gensym85.elems := {p};
              gensym85.left := null;
              gensym85.right := null;
              gensym86.data := q;
              gensym86.elems := {q};
              gensym86.left := null;
              gensym86.right := null;
              this.data := r;
              this.elems := {p, q, r};
              this.left := gensym86;
              this.right := gensym85;
              // repr stuff
              gensym85.Repr := {gensym85};
              gensym86.Repr := {gensym86};
              this.Repr := ({this} + this.left.Repr) + this.right.Repr;
            } else {
              var gensym82 := new SetNode;
              var gensym83 := new SetNode;
              gensym82.data := p;
              gensym82.elems := {p};
              gensym82.left := null;
              gensym82.right := null;
              gensym83.data := r;
              gensym83.elems := {r};
              gensym83.left := null;
              gensym83.right := null;
              this.data := q;
              this.elems := {p, q, r};
              this.left := gensym83;
              this.right := gensym82;
              // repr stuff
              gensym82.Repr := {gensym82};
              gensym83.Repr := {gensym83};
              this.Repr := ({this} + this.left.Repr) + this.right.Repr;
            }
          }
        }
      }
    }
  }

}


