class Node<T> {
  var list: seq<T>;
  var footprint: set<Node<T>>;

  var data: T;
  var next: Node<T>;

  function Valid(): bool
    reads this, footprint;
  {
    this in this.footprint && null !in this.footprint &&
    (next == null ==> list == [data]) &&
    (next != null ==>
        next in footprint && next.footprint <= footprint &&
        this !in next.footprint &&
        list == [data] + next.list &&
        next.Valid())
  }

  method Init(d: T)
    modifies this;
    ensures Valid() && fresh(footprint - {this});
    ensures list == [d];
  {
    data := d;
    next := null;
    list := [d];
    footprint := {this};
  }

  method SkipHead() returns (r: Node<T>)
    requires Valid();
    ensures r == null ==> |list| == 1;
    ensures r != null ==> r.Valid() && r.footprint <= footprint;
    ensures r != null ==> r.list == list[1..];
  {
    r := next;
  }

  method Prepend(d: T) returns (r: Node<T>)
    requires Valid();
    ensures r != null && r.Valid() && fresh(r.footprint - old(footprint));
    ensures r.list == [d] + list;
  {
    r := new Node<T>;
    r.data := d;
    r.next := this;
    r.footprint := {r} + this.footprint;
    r.list := [r.data] + this.list;
  }

  method ReverseInPlace() returns (reverse: Node<T>)
    requires Valid();
    modifies footprint;
    ensures reverse != null && reverse.Valid();
    ensures fresh(reverse.footprint - old(footprint));
    ensures |reverse.list| == |old(list)|;
    ensures (forall i :: 0 <= i && i < |old(list)| ==> old(list)[i] == reverse.list[|old(list)|-1-i]);
  {
    var current := next;
    reverse := this;
    reverse.next := null;
    reverse.footprint := {reverse};
    reverse.list := [data];

    while (current != null)
      invariant reverse != null && reverse.Valid();
      invariant reverse.footprint <= old(footprint);
      invariant current == null ==> |old(list)| == |reverse.list|;
      invariant current != null ==>
        current.Valid() &&
        current in old(footprint) && current.footprint <= old(footprint) &&
        current.footprint !! reverse.footprint &&
        |old(list)| == |reverse.list| + |current.list| &&
        (forall i :: 0 <= i && i < |current.list| ==> current.list[i] == old(list)[|reverse.list|+i]);
      invariant
        (forall i :: 0 <= i && i < |reverse.list| ==> old(list)[i] == reverse.list[|reverse.list|-1-i]);
      decreases if current != null then |current.list| else -1;
    {
      var nx := current.next;

      // ..., reverse, current, nx, ...
      current.next := reverse;
      current.footprint := {current} + reverse.footprint;
      current.list := [current.data] + reverse.list;

      reverse := current;
      current := nx;
    }
  }
}
