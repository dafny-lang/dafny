class DList<T> {
  ghost var Repr: set<object>;
  ghost var list: seq<T>;

  var root: DNode<T>;

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
    ensures list[0] == p;
    ensures list[1] == q;
    ensures |list| == 2;
  {
    var gensym79 := new DNode<T>;
    var gensym85 := new DNode<T>;
    this.list := [p, q];
    this.root := gensym79;
    gensym79.data := p;
    gensym79.list := [p, q];
    gensym79.next := gensym85;
    gensym79.prev := null;
    gensym85.data := q;
    gensym85.list := [q];
    gensym85.next := null;
    gensym85.prev := gensym79;

    // repr stuff
    gensym85.Repr := {gensym85};
    gensym79.Repr := {gensym79} + {gensym85};
    this.Repr := {this} + ({gensym79} + {gensym85});
    // assert repr objects are valid (helps verification)
    assert gensym79.Valid() && gensym85.Valid();
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


  method Singleton(t: T)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [t];
    ensures list[0] == t;
    ensures |list| == 1;
  {
    var gensym78 := new DNode<T>;
    this.list := [t];
    this.root := gensym78;
    gensym78.data := t;
    gensym78.list := [t];
    gensym78.next := null;
    gensym78.prev := null;

    // repr stuff
    gensym78.Repr := {gensym78};
    this.Repr := {this} + {gensym78};
    // assert repr objects are valid (helps verification)
    assert gensym78.Valid();
  }

}

class DNode<T> {
  ghost var Repr: set<object>;
  ghost var list: seq<T>;

  var data: T;
  var next: DNode<T>;
  var prev: DNode<T>;

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
    (next != null ==> list == [data] + next.list && next.prev == this) &&
    (prev != null ==> prev.next == this) &&
    (|list| > 0)
  }

  function Valid(): bool
    reads *;
    decreases Repr;
  {
    this.Valid_self() &&
    (next != null ==> next.Valid()) &&
    (next != null ==> next.Valid_self()) &&
    (next != null && next.next != null ==> next.next.Valid_self())
  }


  method Double(p: T, q: T)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [p, q];
    ensures list[0] == p;
    ensures list[1] == q;
    ensures |list| == 2;
  {
    var gensym95 := new DNode<T>;
    this.data := p;
    this.list := [p, q];
    this.next := gensym95;
    this.prev := null;
    gensym95.data := q;
    gensym95.list := [q];
    gensym95.next := null;
    gensym95.prev := this;

    // repr stuff
    this.Repr := {this} + {gensym95};
    gensym95.Repr := {gensym95};
    // assert repr objects are valid (helps verification)
    assert gensym95.Valid();
  }


  method Find(n: T) returns (ret: bool)
    requires Valid();
    ensures fresh(Repr - old(Repr));
    ensures Valid();
    ensures ret == (n in list);
    decreases Repr;
  {
    if (this.next == null) {
      ret := n == this.data;
    } else {
      var x_5 := this.next.Find(n);
      ret := n == this.data || x_5;
    }
  }


  method Get(idx: int) returns (ret: T)
    requires Valid();
    requires idx >= 0;
    requires idx < |list|;
    ensures fresh(Repr - old(Repr));
    ensures Valid();
    ensures ret == list[idx];
    decreases Repr;
  {
    if (this.next == null) {
      ret := this.data;
    } else {
      if (idx == 0) {
        ret := this.data;
      } else {
        var x_6 := this.next.Get(idx - 1);
        ret := x_6;
      }
    }
  }


  method Init(t: T)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [t];
    ensures list[0] == t;
    ensures |list| == 1;
  {
    this.data := t;
    this.list := [t];
    this.next := null;
    this.prev := null;

    // repr stuff
    this.Repr := {this};
  }


  method List() returns (ret: seq<T>)
    requires Valid();
    ensures fresh(Repr - old(Repr));
    ensures Valid();
    ensures ret == list;
    decreases Repr;
  {
    if (this.next == null) {
      ret := [this.data];
    } else {
      var x_7 := this.next.List();
      ret := [this.data] + x_7;
    }
  }


  method Size() returns (ret: int)
    requires Valid();
    ensures fresh(Repr - old(Repr));
    ensures Valid();
    ensures ret == |list|;
    decreases Repr;
  {
    if (this.next == null) {
      ret := 1;
    } else {
      var x_8 := this.next.Size();
      ret := 1 + x_8;
    }
  }

}


