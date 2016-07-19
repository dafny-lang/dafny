class List<T> {
  ghost var Repr: set<object>;
  ghost var list: seq<T>;

  var data: T;
  var next: List<T>;

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


  method Dupleton(p: T, q: T)
    modifies this;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures list == [p, q];
    ensures list[0] == p;
    ensures list[1] == q;
    ensures |list| == 2;
  {
    var gensym71 := new List<T>;
    gensym71.Singleton(q);
    this.data := p;
    this.list := [p, q];
    this.next := gensym71;

    // repr stuff
    this.Repr := {this} + this.next.Repr;
    // assert repr objects are valid (helps verification)
    assert gensym71.Valid();
  }


  method Elems() returns (ret: seq<T>)
    requires Valid();
    ensures fresh(Repr - old(Repr));
    ensures Valid();
    ensures ret == list;
    decreases Repr;
  {
    if (this.next == null) {
      ret := [this.data];
    } else {
      var x_5 := this.next.Elems();
      ret := [this.data] + x_5;
    }
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
      var x_6 := this.next.Find(n);
      ret := n == this.data || x_6;
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
        var x_7 := this.next.Get(idx - 1);
        ret := x_7;
      }
    }
  }


  method Singleton(t: T)
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


