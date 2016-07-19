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


  method Double(p: T, q: T)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [p, q];
  {
    var gensym68 := new Node<T>;
    gensym68._synth_List_Double_gensym68(p, q);
    this.list := [p, q];
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


  method Singleton(t: T)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [t];
  {
    var gensym69 := new Node<T>;
    gensym69._synth_List_Singleton_gensym69(t);
    this.list := [t];
    this.root := gensym69;
    // repr stuff
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
    (next != null ==> next.Valid_self()) &&
    (next != null && next.next != null ==> next.next.Valid_self())
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


  method _synth_List_Double_gensym68(p: T, q: T)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures |list| == 2;
    ensures list[0] == p;
    ensures list[1] == q;
  {
    var gensym75 := new Node<T>;
    gensym75._synth_Node__synth_List_Double_gensym68_gensym75(q);
    this.data := p;
    this.list := [p, q];
    this.next := gensym75;
    // repr stuff
    this.Repr := {this} + this.next.Repr;
  }


  method _synth_List_Singleton_gensym69(t: T)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures |list| == 1;
    ensures list[0] == t;
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
    var gensym73 := new Node<T>;
    gensym73._synth_Node_Double_gensym73(q);
    this.data := p;
    this.list := [p, q];
    this.next := gensym73;
    // repr stuff
    this.Repr := {this} + this.next.Repr;
  }


  method _synth_Node_Double_gensym73(q: T)
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


  method _synth_Node__synth_List_Double_gensym68_gensym75(q: T)
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

}


