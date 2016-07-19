class DList<T> {
  ghost var Repr: set<object>;
  ghost var list: seq<T>;

  var data: T;
  var next: DList<T>;
  var prev: DList<T>;

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
    var gensym71 := new DList<T>;
    this.data := p;
    this.list := [p, q];
    this.next := gensym71;
    this.prev := null;
    gensym71.data := q;
    gensym71.list := [q];
    gensym71.next := null;
    gensym71.prev := this;

    // repr stuff
    this.Repr := {this} + {gensym71};
    gensym71.Repr := {gensym71};
    // assert repr objects are valid (helps verification)
    assert gensym71.Valid();
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
    requires 0 <= idx;
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


