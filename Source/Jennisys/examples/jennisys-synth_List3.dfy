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
    (root != null ==> |list| == |root.succ| + 1 && (list[0] == root.data && (forall i: int :: 0 < i && i <= |root.succ| ==> root.succ[i - 1] != null && list[i] == root.succ[i - 1].data)))
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
    ensures list == [];
  {
    this.list := [];
    this.root := null;
    // repr stuff
    this.Repr := {this};
  }

  method SingletonTwo()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [2];
  {
    var gensym65 := new IntNode;
    gensym65.data := 2;
    gensym65.next := null;
    gensym65.succ := [];
    this.list := [2];
    this.root := gensym65;
    // repr stuff
    gensym65.Repr := {gensym65};
    this.Repr := {this} + this.root.Repr;
  }

  method OneTwo()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [1] + [2];
  {
    var gensym63 := new IntNode;
    var gensym75 := new IntNode;
    gensym63.data := 1;
    gensym63.next := gensym75;
    gensym63.succ := [gensym75];
    gensym75.data := 2;
    gensym75.next := null;
    gensym75.succ := [];
    this.list := [1, 2];
    this.root := gensym63;
    // repr stuff
    gensym75.Repr := {gensym75};
    gensym63.Repr := {gensym63} + gensym63.next.Repr;
    this.Repr := {this} + this.root.Repr;
  }

  method Singleton(p: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [p];
  {
    var gensym66 := new IntNode;
    gensym66.data := p;
    gensym66.next := null;
    gensym66.succ := [];
    this.list := [p];
    this.root := gensym66;
    // repr stuff
    gensym66.Repr := {gensym66};
    this.Repr := {this} + this.root.Repr;
  }

  method TwoConsecutive(p: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [p] + [p + 1];
  {
    var gensym64 := new IntNode;
    var gensym75 := new IntNode;
    gensym64.data := p;
    gensym64.next := gensym75;
    gensym64.succ := [gensym75];
    gensym75.data := p + 1;
    gensym75.next := null;
    gensym75.succ := [];
    this.list := [p] + [p + 1];
    this.root := gensym64;
    // repr stuff
    gensym75.Repr := {gensym75};
    gensym64.Repr := {gensym64} + gensym64.next.Repr;
    this.Repr := {this} + this.root.Repr;
  }

  method Double(p: int, q: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [p] + [q];
  {
    var gensym65 := new IntNode;
    var gensym77 := new IntNode;
    gensym65.data := p;
    gensym65.next := gensym77;
    gensym65.succ := [gensym77];
    gensym77.data := q;
    gensym77.next := null;
    gensym77.succ := [];
    this.list := [p] + [q];
    this.root := gensym65;
    // repr stuff
    gensym77.Repr := {gensym77};
    gensym65.Repr := {gensym65} + gensym65.next.Repr;
    this.Repr := {this} + this.root.Repr;
  }

  method Sum(p: int, q: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [p + q];
  {
    var gensym67 := new IntNode;
    gensym67.data := p + q;
    gensym67.next := null;
    gensym67.succ := [];
    this.list := [p + q];
    this.root := gensym67;
    // repr stuff
    gensym67.Repr := {gensym67};
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
    (next != null ==> next.Valid_self() && (next.next != null ==> next.next.Valid_self()))
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

  method OneTwo()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures data == 1;
    ensures |succ| == 1;
    ensures succ[0] != null;
    ensures succ[0].data == 2;
  {
    var gensym71 := new IntNode;
    gensym71.data := 2;
    gensym71.next := null;
    gensym71.succ := [];
    this.data := 1;
    this.next := gensym71;
    this.succ := [gensym71];
    // repr stuff
    gensym71.Repr := {gensym71};
    this.Repr := {this} + this.next.Repr;
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

}


