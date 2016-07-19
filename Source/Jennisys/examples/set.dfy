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
    gensym66.Init(t);
    this.elems := {t};
    this.root := gensym66;
    this.Repr := {this} + this.root.Repr;
  }

  method Sum(p: int, q: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {p + q};
  {
    var gensym68 := new SetNode;
    gensym68.Init(p+q);
    this.elems := {p + q};
    this.root := gensym68;
    this.Repr := {this} + this.root.Repr;
  }

  method Double(p: int, q: int)
    modifies this;
    requires p != q;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {p, q};
  {
    var gensym71 := new SetNode; 
    gensym71.Double(p, q);
    this.elems := {p, q}; 
    this.root := gensym71; 
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
//    requires p != q;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {p, q};
  {
    if (q > p) {
      var gensym79 := new SetNode;
      gensym79.Init(q);
      this.data := p;
      this.elems := {p, q};
      this.left := null;
      this.right := gensym79;
      this.Repr := {this} + this.right.Repr;
    } else if (q < p) {
      var gensym79 := new SetNode;
      gensym79.Init(p);
      this.data := q;
      this.elems := {p, q};
      this.left := null;
      this.right := gensym79;
      this.Repr := {this} + this.right.Repr;
    } else {
      this.data := p; 
      this.elems := {p};
      this.left := null;
      this.right := null;
      this.Repr := {this};
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
      gensym83.Init(r);
      gensym84.Init(p);
      this.data := q;
      this.elems := {p, q, r};
      this.left := gensym84;
      this.right := gensym83;
      this.Repr := ({this} + this.left.Repr) + this.right.Repr;
    } else {
      if (p < r && q > r) {
        var gensym85 := new SetNode;
        var gensym86 := new SetNode;
        gensym85.Init(q);
        gensym86.Init(p);
        this.data := r;
        this.elems := {p, q, r};
        this.left := gensym86;
        this.right := gensym85;
        this.Repr := ({this} + this.left.Repr) + this.right.Repr;
      } else {
        if (r < p && q > p) {
          var gensym84 := new SetNode;
          var gensym85 := new SetNode;
          gensym84.Init(q);
          gensym85.Init(r);
          this.data := p;
          this.elems := {p, q, r};
          this.left := gensym85;
          this.right := gensym84;
          this.Repr := ({this} + this.left.Repr) + this.right.Repr;
        } else {
          if (q < p && r > p) {
            var gensym82 := new SetNode;
            var gensym83 := new SetNode;
            gensym82.Init(r);
            gensym83.Init(q);
            this.data := p;
            this.elems := {p, q, r};
            this.left := gensym83;
            this.right := gensym82;
            this.Repr := ({this} + this.left.Repr) + this.right.Repr;
          } else {
            if (q < r && p > r) {
              var gensym85 := new SetNode;
              var gensym86 := new SetNode;
              gensym85.Init(p);
              gensym86.Init(q);
              this.data := r;
              this.elems := {p, q, r};
              this.left := gensym86;
              this.right := gensym85;
              this.Repr := ({this} + this.left.Repr) + this.right.Repr;
            } else {
              var gensym82 := new SetNode;
              var gensym83 := new SetNode;
              gensym82.Init(p);
              gensym83.Init(r);
              this.data := q;
              this.elems := {p, q, r};
              this.left := gensym83;
              this.right := gensym82;
              this.Repr := ({this} + this.left.Repr) + this.right.Repr;
            }
          }
        }
      }
    }
  }

}


