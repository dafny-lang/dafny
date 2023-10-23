// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Collection<T> {
  ghost var footprint:set<object>
  var elements:seq<T>

  ghost predicate Valid()
    reads this, footprint
  {
    this in footprint
  }

  method GetCount() returns (c:nat)
    requires Valid()
  {
    c:=|elements|;
  }

  method Init()
    modifies this
    ensures Valid() && fresh(footprint - {this})
  {
    elements := [];
    footprint := {this};
  }

  method GetItem(i:int) returns (x:T)
    requires Valid()
    requires 0 <= i < |elements|
    ensures elements[i] == x
  {
    x:=elements[i];
  }

  method Add(x:T)
    requires Valid()
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures elements == old(elements) + [x]
  {
    elements:= elements + [x];
  }

  method GetIterator() returns (iter:Iterator<T>)
    requires Valid()
    ensures iter.Valid()
    ensures fresh(iter.footprint) && iter.pos == -1
    ensures iter.c == this
  {
    iter:= new Iterator<T>.Init(this);
  }

}

class Iterator<T> {

  var c:Collection<T>
  var pos:int

  ghost var footprint:set<object>

  ghost predicate Valid()
    reads this, footprint
  {
    this in footprint && -1 <= pos
  }

  constructor Init(coll:Collection<T>)
    ensures Valid() && fresh(footprint - {this}) && pos == -1
    ensures c == coll
  {
    c := coll;
    pos := -1;
    footprint := {this};
  }

  method MoveNext() returns (b:bool)
    requires Valid()
    modifies footprint
    ensures fresh(footprint - old(footprint)) && Valid() && pos == old(pos) + 1
    ensures b == HasCurrent() && c == old(c)
  {
    pos := pos+1;
    b := pos < |c.elements|;
  }

  ghost predicate HasCurrent()
    requires Valid()
    reads this, c, footprint
  {
    0 <= pos && pos < |c.elements|
  }

  method GetCurrent() returns (x:T)
    requires Valid() && HasCurrent()
    ensures c.elements[pos] == x
  {
    x := c.elements[pos];
  }
}

class Client
{
  method Main()
  {
    var c := new Collection<int>.Init();
    c.Add(33);
    c.Add(45);
    c.Add(78);

    var s := [];

    var iter := c.GetIterator();
    var b := iter.MoveNext();

    while (b)
      invariant iter.Valid() && b == iter.HasCurrent() && fresh(iter.footprint)
      invariant c.Valid() && fresh(c.footprint) && iter.footprint !! c.footprint //disjoint footprints
      invariant 0 <= iter.pos && iter.pos <= |c.elements| && s == c.elements[..iter.pos]
      invariant iter.c == c
      decreases |c.elements| - iter.pos
    {
      var x := iter.GetCurrent();
      s := s + [x];
      b := iter.MoveNext();
    }

    assert s == c.elements; //verifies that the iterator returns the correct things
    c.Add(100);
  }

}
