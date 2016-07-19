class List<T> {
  ghost var Repr: set<object>;
  ghost var list: seq<T>;

  var root: Node<T>;

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

  method Singleton(t: T)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [t];
  {
    var gensym65 := new Node<T>;
    gensym65.data := t;
    gensym65.list := [t];
    gensym65.next := null;
    this.list := [t];
    this.root := gensym65;
    // repr stuff
    gensym65.Repr := {gensym65};
    this.Repr := {this} + this.root.Repr;
  }

  method Double(p: T, q: T)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [p, q];
  {
    var gensym66 := new Node<T>;
    var gensym67 := new Node<T>;
    gensym66.data := p;
    gensym66.list := [p, q];
    gensym66.next := gensym67;
    gensym67.data := q;
    gensym67.list := [q];
    gensym67.next := null;
    this.list := [p, q];
    this.root := gensym66;
    // repr stuff
    gensym67.Repr := {gensym67};
    gensym66.Repr := {gensym66} + gensym66.next.Repr;
    this.Repr := {this} + this.root.Repr;
  }

}

class Node<T> {
  ghost var Repr: set<object>;
  ghost var list: seq<T>;

  var data: T;
  var next: Node<T>;

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
    (next == null <==> list == [data] && list[0] == data) &&
    (next != null ==> list == [data] + next.list) &&
    (|list| > 0)
  }

  function Valid(): bool
    reads *;
  {
    this.Valid_self() &&
    (next != null ==> next.Valid_self() && (next.next != null ==> next.next.Valid_self()))
  }

  method Init(t: T)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [t];
  {
    this.data := t;
    this.list := [t];
    this.next := null;
    // repr stuff
    this.Repr := {this};
  }

  method Double(p: T, q: T)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [p, q];
  {
    var gensym71 := new Node<T>;
    gensym71.data := q;
    gensym71.list := [q];
    gensym71.next := null;
    this.data := p;
    this.list := [p, q];
    this.next := gensym71;
    // repr stuff
    gensym71.Repr := {gensym71};
    this.Repr := {this} + this.next.Repr;
  }

}


