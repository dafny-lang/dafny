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
    gensym67.Double(p, q);
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
    gensym65.Double(1, 2);
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
    var gensym66 := new IntNode;
    gensym66.Init(p);
    this.list := [p];
    this.root := gensym66;
    // repr stuff
    this.Repr := {this} + this.root.Repr;
  }


  method SingletonTwo()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [2];
  {
    var gensym65 := new IntNode;
    gensym65.Init(2);
    this.list := [2];
    this.root := gensym65;
    // repr stuff
    this.Repr := {this} + this.root.Repr;
  }


  method Sum(p: int, q: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [p + q];
  {
    var gensym67 := new IntNode;
    gensym67.Init(p + q);
    this.list := [p + q];
    this.root := gensym67;
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
    gensym66.Double(p, p + 1);
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
    (next == null ==> (list == [data] && list[0] == data) && |list| == 1) &&
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


  method Double(x: int, y: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [x, y];
  {
    var gensym74 := new IntNode;
    gensym74.Init(y);
    this.data := x;
    this.list := [x, y];
    this.next := gensym74;
    // repr stuff
    this.Repr := {this} + this.next.Repr;
  }


  method Init(x: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [x];
  {
    this.data := x;
    this.list := [x];
    this.next := null;
    // repr stuff
    this.Repr := {this};
  }

}


