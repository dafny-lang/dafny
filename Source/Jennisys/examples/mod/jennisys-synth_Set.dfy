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
    gensym67._synth_Set_Double_gensym67(p, q);
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
    gensym67._synth_Set_Singleton_gensym67(t);
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
    gensym69._synth_Set_Sum_gensym69(p, q);
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


  method Double(p: int, q: int)
    modifies this;
    requires p != q;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {p, q};
  {
    if (q > p) {
      var gensym77 := new SetNode;
      gensym77._synth_SetNode_Double_gensym77(q);
      this.data := p;
      this.elems := {p, q};
      this.left := null;
      this.right := gensym77;
      // repr stuff
      this.Repr := {this} + this.right.Repr;
    } else {
      var gensym77 := new SetNode;
      gensym77._synth_SetNode_Double_gensym77(p);
      this.data := q;
      this.elems := {p, q};
      this.left := null;
      this.right := gensym77;
      // repr stuff
      this.Repr := {this} + this.right.Repr;
    }
  }


  method _synth_SetNode_Double_gensym77(q: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {q};
  {
    this.data := q;
    this.elems := {q};
    this.left := null;
    this.right := null;
    // repr stuff
    this.Repr := {this};
  }


  method _synth_SetNode_Triple_gensym80(r: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {r};
  {
    this.data := r;
    this.elems := {r};
    this.left := null;
    this.right := null;
    // repr stuff
    this.Repr := {this};
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
      var gensym80 := new SetNode;
      var gensym81 := new SetNode;
      gensym80._synth_SetNode_Triple_gensym80(r);
      gensym81._synth_SetNode_Triple_gensym81(p);
      this.data := q;
      this.elems := {p, q, r};
      this.left := gensym81;
      this.right := gensym80;
      // repr stuff
      this.Repr := ({this} + this.left.Repr) + this.right.Repr;
    } else {
      if (r < p && q > p) {
        var gensym80 := new SetNode;
        var gensym81 := new SetNode;
        gensym80._synth_SetNode_Triple_gensym80(q);
        gensym81._synth_SetNode_Triple_gensym81(r);
        this.data := p;
        this.elems := {p, q, r};
        this.left := gensym81;
        this.right := gensym80;
        // repr stuff
        this.Repr := ({this} + this.left.Repr) + this.right.Repr;
      } else {
        if (p < r && q > r) {
          var gensym80 := new SetNode;
          var gensym81 := new SetNode;
          gensym80._synth_SetNode_Triple_gensym80(q);
          gensym81._synth_SetNode_Triple_gensym81(p);
          this.data := r;
          this.elems := {p, q, r};
          this.left := gensym81;
          this.right := gensym80;
          // repr stuff
          this.Repr := ({this} + this.left.Repr) + this.right.Repr;
        } else {
          if (r < q && p > q) {
            var gensym80 := new SetNode;
            var gensym81 := new SetNode;
            gensym80._synth_SetNode_Triple_gensym80(p);
            gensym81._synth_SetNode_Triple_gensym81(r);
            this.data := q;
            this.elems := {p, q, r};
            this.left := gensym81;
            this.right := gensym80;
            // repr stuff
            this.Repr := ({this} + this.left.Repr) + this.right.Repr;
          } else {
            if (q < r && p > r) {
              var gensym80 := new SetNode;
              var gensym81 := new SetNode;
              gensym80._synth_SetNode_Triple_gensym80(p);
              gensym81._synth_SetNode_Triple_gensym81(q);
              this.data := r;
              this.elems := {p, q, r};
              this.left := gensym81;
              this.right := gensym80;
              // repr stuff
              this.Repr := ({this} + this.left.Repr) + this.right.Repr;
            } else {
              var gensym80 := new SetNode;
              var gensym81 := new SetNode;
              gensym80._synth_SetNode_Triple_gensym80(r);
              gensym81._synth_SetNode_Triple_gensym81(q);
              this.data := p;
              this.elems := {p, q, r};
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


  method _synth_SetNode_Triple_gensym81(p: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {p};
  {
    this.data := p;
    this.elems := {p};
    this.left := null;
    this.right := null;
    // repr stuff
    this.Repr := {this};
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


  method _synth_SetNode__synth_Set_Double_gensym67_gensym77(q: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {q};
  {
    this.data := q;
    this.elems := {q};
    this.left := null;
    this.right := null;
    // repr stuff
    this.Repr := {this};
  }


  method _synth_Set_Double_gensym67(p: int, q: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {p, q};
  {
    if (q > p) {
      var gensym77 := new SetNode;
      gensym77._synth_SetNode__synth_Set_Double_gensym67_gensym77(q);
      this.data := p;
      this.elems := {p, q};
      this.left := null;
      this.right := gensym77;
      // repr stuff
      this.Repr := {this} + this.right.Repr;
    } else {
      if (p > q) {
        var gensym77 := new SetNode;
        gensym77._synth_SetNode__synth_Set_Double_gensym67_gensym77(p);
        this.data := q;
        this.elems := {p, q};
        this.left := null;
        this.right := gensym77;
        // repr stuff
        this.Repr := {this} + this.right.Repr;
      } else {
        this.data := q;
        this.elems := {p, q};
        this.left := null;
        this.right := null;
        // repr stuff
        this.Repr := {this};
      }
    }
  }


  method _synth_Set_Singleton_gensym67(t: int)
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


  method _synth_Set_Sum_gensym69(p: int, q: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {p + q};
  {
    this.data := p + q;
    this.elems := {p + q};
    this.left := null;
    this.right := null;
    // repr stuff
    this.Repr := {this};
  }

}


