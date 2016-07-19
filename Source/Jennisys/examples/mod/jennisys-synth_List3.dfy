class IntList {
  ghost var Repr: set<object>;
  ghost var list: seq<int>;

  var root: IntNode;

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
    (root == null ==> |list| == 0) &&
    (root != null ==> |list| == |root.succ| + 1 && (list[0] == root.data && (forall i :: 1 <= i && i <= |root.succ| ==> root.succ[i - 1] != null && list[i] == root.succ[i - 1].data)))
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
    ensures list == [p] + [q];
  {
    var gensym68 := new IntNode;
    gensym68._synth_IntList_Double_gensym68(p, q);
    this.list := [p] + [q];
    this.root := gensym68;
    // repr stuff
    this.Repr := {this} + this.root.Repr;
  }


  method Empty()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [];
  {
    this.list := [];
    this.root := null;
    // repr stuff
    this.Repr := {this};
  }


  method OneTwo()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [1, 2];
  {
    var gensym65 := new IntNode;
    gensym65._synth_IntList_OneTwo_gensym65();
    this.list := [1, 2];
    this.root := gensym65;
    // repr stuff
    this.Repr := {this} + this.root.Repr;
  }


  method Singleton(p: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [p];
  {
    var gensym70 := new IntNode;
    gensym70._synth_IntList_Singleton_gensym70(p);
    this.list := [p];
    this.root := gensym70;
    // repr stuff
    this.Repr := {this} + this.root.Repr;
  }


  method SingletonTwo()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [2];
  {
    var gensym69 := new IntNode;
    gensym69._synth_IntList_SingletonTwo_gensym69();
    this.list := [2];
    this.root := gensym69;
    // repr stuff
    this.Repr := {this} + this.root.Repr;
  }


  method Sum(p: int, q: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [p + q];
  {
    var gensym71 := new IntNode;
    gensym71._synth_IntList_Sum_gensym71(p, q);
    this.list := [p + q];
    this.root := gensym71;
    // repr stuff
    this.Repr := {this} + this.root.Repr;
  }


  method TwoConsecutive(p: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [p] + [p + 1];
  {
    var gensym67 := new IntNode;
    gensym67._synth_IntList_TwoConsecutive_gensym67(p);
    this.list := [p] + [p + 1];
    this.root := gensym67;
    // repr stuff
    this.Repr := {this} + this.root.Repr;
  }

}

class IntNode {
  ghost var Repr: set<object>;
  ghost var succ: seq<IntNode>;
  ghost var data: int;

  var next: IntNode;

  function Valid_repr(): bool
    reads *;
  {
    this in Repr &&
    null !in Repr &&
    (next != null ==> next in Repr && next.Repr <= Repr && this !in next.Repr)
  }

  function Valid_self(): bool
    reads *;
  {
    Valid_repr() &&
    (next == null ==> |succ| == 0) &&
    (next != null ==> succ == [next] + next.succ) &&
    (!(null in succ))
  }

  function Valid(): bool
    reads *;
  {
    this.Valid_self() &&
    (next != null ==> next.Valid_self()) &&
    (next != null && next.next != null ==> next.next.Valid_self())
  }


  method Init(p: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures data == p;
  {
    this.data := p;
    this.next := null;
    this.succ := [];
    // repr stuff
    this.Repr := {this};
  }


  method InitInc(p: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures data == p + 1;
  {
    this.data := p + 1;
    this.next := null;
    this.succ := [];
    // repr stuff
    this.Repr := {this};
  }


  method Zero()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures data == 0;
    ensures succ == [];
  {
    this.data := 0;
    this.next := null;
    this.succ := [];
    // repr stuff
    this.Repr := {this};
  }


  method _synth_IntList_Double_gensym68(p: int, q: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures data == p;
    ensures |succ| == 1;
    ensures succ[0].data == q;
    ensures succ[0].succ == [];
  {
    var gensym80 := new IntNode;
    gensym80._synth_IntNode__synth_IntList_Double_gensym68_gensym80(q);
    this.data := p;
    this.next := gensym80;
    this.succ := [gensym80];
    // repr stuff
    this.Repr := {this} + this.next.Repr;
  }


  method _synth_IntList_OneTwo_gensym65()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures data == 1;
    ensures |succ| == 1;
    ensures succ[0].data == 2;
    ensures succ[0].succ == [];
  {
    var gensym78 := new IntNode;
    gensym78._synth_IntNode__synth_IntList_OneTwo_gensym65_gensym78();
    this.data := 1;
    this.next := gensym78;
    this.succ := [gensym78];
    // repr stuff
    this.Repr := {this} + this.next.Repr;
  }


  method _synth_IntList_SingletonTwo_gensym69()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures data == 2;
    ensures |succ| == 0;
  {
    this.data := 2;
    this.next := null;
    this.succ := [];
    // repr stuff
    this.Repr := {this};
  }


  method _synth_IntList_Singleton_gensym70(p: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures data == p;
    ensures |succ| == 0;
  {
    this.data := p;
    this.next := null;
    this.succ := [];
    // repr stuff
    this.Repr := {this};
  }


  method _synth_IntList_Sum_gensym71(p: int, q: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures data == p + q;
    ensures |succ| == 0;
  {
    this.data := p + q;
    this.next := null;
    this.succ := [];
    // repr stuff
    this.Repr := {this};
  }


  method _synth_IntList_TwoConsecutive_gensym67(p: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures data == p;
    ensures |succ| == 1;
    ensures succ[0].data == p + 1;
    ensures succ[0].succ == [];
  {
    var gensym79 := new IntNode;
    gensym79._synth_IntNode__synth_IntList_TwoConsecutive_gensym67_gensym79(p);
    this.data := p;
    this.next := gensym79;
    this.succ := [gensym79];
    // repr stuff
    this.Repr := {this} + this.next.Repr;
  }


  method OneTwo()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures data == 1;
    ensures |succ| == 1;
    ensures succ[0] != null;
    ensures succ[0].data == 2;
  {
    var gensym73 := new IntNode;
    gensym73._synth_IntNode_OneTwo_gensym73();
    this.data := 1;
    this.next := gensym73;
    this.succ := [gensym73];
    // repr stuff
    this.Repr := {this} + this.next.Repr;
  }


  method _synth_IntNode_OneTwo_gensym73()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures data == 2;
    ensures |succ| == 0;
  {
    this.data := 2;
    this.next := null;
    this.succ := [];
    // repr stuff
    this.Repr := {this};
  }


  method _synth_IntNode__synth_IntList_Double_gensym68_gensym80(q: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures data == q;
    ensures |succ| == 0;
  {
    this.data := q;
    this.next := null;
    this.succ := [];
    // repr stuff
    this.Repr := {this};
  }


  method _synth_IntNode__synth_IntList_OneTwo_gensym65_gensym78()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures data == 2;
    ensures |succ| == 0;
  {
    this.data := 2;
    this.next := null;
    this.succ := [];
    // repr stuff
    this.Repr := {this};
  }


  method _synth_IntNode__synth_IntList_TwoConsecutive_gensym67_gensym79(p: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures data == p + 1;
    ensures |succ| == 0;
  {
    this.data := p + 1;
    this.next := null;
    this.succ := [];
    // repr stuff
    this.Repr := {this};
  }

}


