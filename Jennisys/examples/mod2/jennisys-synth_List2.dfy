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
    ensures list[0] == p;
    ensures list[1] == q;
    ensures |list| == 2;
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


  method Double(x: int, y: int)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [x, y];
    ensures list[0] == x;
    ensures list[1] == y;
    ensures |list| == 2;
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
    ensures list[0] == x;
    ensures |list| == 1;
  {
    this.data := x;
    this.list := [x];
    this.next := null;
    // repr stuff
    this.Repr := {this};
  }


  method SingletonZero()
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [0];
    ensures list[0] == 0;
    ensures |list| == 1;
  {
    this.Init(0);
  }

}


