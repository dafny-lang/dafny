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
    ensures list[0] == p;
    ensures list[1] == q;
    ensures |list| == 2;
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
    ensures |list| == 0;
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
    ensures list[0] == 1;
    ensures list[1] == 2;
    ensures |list| == 2;
  {
    this.Double(1, 2);
  }


  method Singleton(p: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [p];
    ensures list[0] == p;
    ensures |list| == 1;
  {
    var gensym67 := new IntNode;
    gensym67._synth_IntList_Singleton_gensym67(p);
    this.list := [p];
    this.root := gensym67;
    // repr stuff
    this.Repr := {this} + this.root.Repr;
  }


  method SingletonTwo()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [2];
    ensures list[0] == 2;
    ensures |list| == 1;
  {
    this.Singleton(2);
  }


  method Sum(p: int, q: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [p + q];
    ensures list[0] == p + q;
    ensures |list| == 1;
  {
    this.Singleton(p + q);
  }


  method TwoConsecutive(p: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [p] + [p + 1];
    ensures list[0] == p;
    ensures list[1] == p + 1;
    ensures |list| == 2;
  {
    this.Double(p, p + 1);
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
    this.Init(p + 1);
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


  method Zero()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures data == 0;
    ensures succ == [];
    ensures |succ| == 0;
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
    ensures |succ[0].succ| == 0;
  {
    var gensym80 := new IntNode;
    gensym80._synth_IntNode__synth_IntList_Double_gensym68_gensym80(q);
    this.data := p;
    this.next := gensym80;
    this.succ := [gensym80];
    // repr stuff
    this.Repr := {this} + this.next.Repr;
  }


  method _synth_IntList_Singleton_gensym67(p: int)
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

}


