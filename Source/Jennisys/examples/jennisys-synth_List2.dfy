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
    gensym65.list := [2];
    gensym65.next := null;
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
    var gensym62 := new IntNode;
    var gensym69 := new IntNode;
    gensym62.data := 1;
    gensym62.list := [1, 2];
    gensym62.next := gensym69;
    gensym69.data := 2;
    gensym69.list := [2];
    gensym69.next := null;
    this.list := [1, 2];
    this.root := gensym62;
    // repr stuff
    gensym69.Repr := {gensym69};
    gensym62.Repr := {gensym62} + gensym62.next.Repr;
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
    gensym66.list := [p];
    gensym66.next := null;
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
    var gensym63 := new IntNode;
    var gensym71 := new IntNode;
    gensym63.data := p;
    gensym63.list := [p] + [p + 1];
    gensym63.next := gensym71;
    gensym71.data := p + 1;
    gensym71.list := [p + 1];
    gensym71.next := null;
    this.list := [p] + [p + 1];
    this.root := gensym63;
    // repr stuff
    gensym71.Repr := {gensym71};
    gensym63.Repr := {gensym63} + gensym63.next.Repr;
    this.Repr := {this} + this.root.Repr;
  }

  method Double(p: int, q: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [p] + [q];
  {
    var gensym64 := new IntNode;
    var gensym71 := new IntNode;
    gensym64.data := p;
    gensym64.list := [p] + [q];
    gensym64.next := gensym71;
    gensym71.data := q;
    gensym71.list := [q];
    gensym71.next := null;
    this.list := [p] + [q];
    this.root := gensym64;
    // repr stuff
    gensym71.Repr := {gensym71};
    gensym64.Repr := {gensym64} + gensym64.next.Repr;
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
    gensym67.list := [p + q];
    gensym67.next := null;
    this.list := [p + q];
    this.root := gensym67;
    // repr stuff
    gensym67.Repr := {gensym67};
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
    (next != null ==> next.Valid_self() && (next.next != null ==> next.next.Valid_self()))
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

}


