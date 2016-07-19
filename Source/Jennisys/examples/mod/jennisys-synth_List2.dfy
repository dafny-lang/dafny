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
    (root == null <==> |list| == 0) &&
    (root != null ==> list == root.list)
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
    var gensym67 := new IntNode;
    gensym67._synth_IntList_Double_gensym67(p, q);
    this.list := [p] + [q];
    this.root := gensym67;
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
    var gensym66 := new IntNode;
    gensym66._synth_IntList_TwoConsecutive_gensym66(p);
    this.list := [p] + [p + 1];
    this.root := gensym66;
    // repr stuff
    this.Repr := {this} + this.root.Repr;
  }

}

class IntNode {
  ghost var Repr: set<object>;
  ghost var list: seq<int>;

  var data: int;
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
    (next == null ==> list == [data] && list[0] == data) &&
    (next != null ==> list == [data] + next.list) &&
    (|list| > 0)
  }

  function Valid(): bool
    reads *;
  {
    this.Valid_self() &&
    (next != null ==> next.Valid_self()) &&
    (next != null && next.next != null ==> next.next.Valid_self())
  }


  method SingletonZero()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [0];
  {
    this.data := 0;
    this.list := [0];
    this.next := null;
    // repr stuff
    this.Repr := {this};
  }


  method _synth_IntList_Double_gensym67(p: int, q: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [p] + [q];
  {
    var gensym78 := new IntNode;
    gensym78._synth_IntNode__synth_IntList_Double_gensym67_gensym78(q);
    this.data := p;
    this.list := [p] + [q];
    this.next := gensym78;
    // repr stuff
    this.Repr := {this} + this.next.Repr;
  }


  method _synth_IntList_OneTwo_gensym65()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures |list| == 2;
    ensures list[0] == 1;
    ensures list[1] == 2;
  {
    var gensym75 := new IntNode;
    gensym75._synth_IntNode__synth_IntList_OneTwo_gensym65_gensym75();
    this.data := 1;
    this.list := [1, 2];
    this.next := gensym75;
    // repr stuff
    this.Repr := {this} + this.next.Repr;
  }


  method _synth_IntList_SingletonTwo_gensym69()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures |list| == 1;
    ensures list[0] == 2;
  {
    this.data := 2;
    this.list := [2];
    this.next := null;
    // repr stuff
    this.Repr := {this};
  }


  method _synth_IntList_Singleton_gensym70(p: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures |list| == 1;
    ensures list[0] == p;
  {
    this.data := p;
    this.list := [p];
    this.next := null;
    // repr stuff
    this.Repr := {this};
  }


  method _synth_IntList_Sum_gensym71(p: int, q: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures |list| == 1;
    ensures list[0] == p + q;
  {
    this.data := p + q;
    this.list := [p + q];
    this.next := null;
    // repr stuff
    this.Repr := {this};
  }


  method _synth_IntList_TwoConsecutive_gensym66(p: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [p] + [p + 1];
  {
    var gensym78 := new IntNode;
    gensym78._synth_IntNode__synth_IntList_TwoConsecutive_gensym66_gensym78(p);
    this.data := p;
    this.list := [p] + [p + 1];
    this.next := gensym78;
    // repr stuff
    this.Repr := {this} + this.next.Repr;
  }


  method _synth_IntNode__synth_IntList_Double_gensym67_gensym78(q: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures |list| == 1;
    ensures list[0] == q;
  {
    this.data := q;
    this.list := [q];
    this.next := null;
    // repr stuff
    this.Repr := {this};
  }


  method _synth_IntNode__synth_IntList_OneTwo_gensym65_gensym75()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures |list| == 1;
    ensures list[0] == 2;
  {
    this.data := 2;
    this.list := [2];
    this.next := null;
    // repr stuff
    this.Repr := {this};
  }


  method _synth_IntNode__synth_IntList_TwoConsecutive_gensym66_gensym78(p: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures |list| == 1;
    ensures list[0] == p + 1;
  {
    this.data := p + 1;
    this.list := [p + 1];
    this.next := null;
    // repr stuff
    this.Repr := {this};
  }

}


