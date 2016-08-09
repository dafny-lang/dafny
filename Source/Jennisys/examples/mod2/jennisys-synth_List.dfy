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
    ensures list[0] == p;
    ensures list[1] == q;
    ensures |list| == 2;
  {
    var gensym78 := new Node<T>;
    gensym78.Double(p, q);
    this.list := [p, q];
    this.root := gensym78;

    // repr stuff
    this.Repr := {this} + this.root.Repr;
    // assert repr objects are valid (helps verification)
    assert gensym78.Valid();
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
    var gensym77 := new Node<T>;
    gensym77.Init(t);
    this.list := [t];
    this.root := gensym77;

    // repr stuff
    this.Repr := {this} + this.root.Repr;
    // assert repr objects are valid (helps verification)
    assert gensym77.Valid();
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
    (next == null ==> (list == [data] && list[0] == data) && |list| == 1) &&
    (next != null ==> list == [data] + next.list) &&
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
    var gensym87 := new Node<T>;
    gensym87.Init(q);
    this.data := p;
    this.list := [p, q];
    this.next := gensym87;

    // repr stuff
    this.Repr := {this} + this.next.Repr;
    // assert repr objects are valid (helps verification)
    assert gensym87.Valid();
  }


  method Find(n: T) returns (ret: bool)
    requires Valid();
    ensures fresh(Repr - old(Repr));
    ensures Valid();
    ensures ret == (n in list);
    decreases Repr;
  {
    if (n != this.data && this.next == null) {
      ret := n == this.data;
    } else {
      if (this.next != null) {
        var x_6 := this.next.Find(n);
        ret := n == this.data || x_6;
      } else {
        ret := true;
      }
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
        var x_7 := this.next.Get(idx - 1);
        ret := x_7;
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
      var x_8 := this.next.List();
      ret := [this.data] + x_8;
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
      var x_9 := this.next.Size();
      ret := 1 + x_9;
    }
  }


  method Tail() returns (tail: Node<T>)
    requires Valid();
    ensures fresh(Repr - old(Repr));
    ensures Valid();
    ensures |list| == 1 ==> tail == null;
    ensures |list| > 1 ==> tail != null && tail.list == list[1..];
    ensures tail != null ==> tail.Valid();
  {
    tail := this.next;
  }

}


