/*
	This test fails with Z3 2.4 (on Win7 x64) and works
	with Z3 2.9 (on Win7 x64). Other versions ... who knows.
*/

// Note: We are using the built-in equality to compare keys.
// Note: The abstract specifications would do well with a map from keys
// to values.  However, Dafny does not support maps.  Instead, such a
// map is modeled by two sequences, one for the keys and one for the values.
// The indices in these sequences correspond, so the dictionary maps
// Keys[i] to Values[i].
// The implementation uses a linked list, which isn't the most efficient
// representation of a dictionary.  However, for the benchmark, it shows
// that the specification can use mathematical sequences while the
// implementation uses a linked list.

class Map<Key(==),Value> {
  ghost var Keys: seq<Key>;
  ghost var Values: seq<Value>;
  ghost var Repr: set<object>;

  var head: Node<Key,Value>;
  ghost var nodes: seq<Node<Key,Value>>;

  function Valid(): bool
    reads this, Repr;
  {
    this in Repr &&
    |Keys| == |Values| && |nodes| == |Keys| + 1 &&
    head == nodes[0] &&
    (forall i :: 0 <= i && i < |Keys| ==>
        nodes[i] != null &&
        nodes[i] in Repr &&
        nodes[i].key == Keys[i] && nodes[i].key !in Keys[i+1..] &&
        nodes[i].val == Values[i] &&
        nodes[i].next == nodes[i+1]) &&
    nodes[|nodes|-1] == null
  }

  method Init()
    modifies this;
    ensures Valid() && fresh(Repr - {this});
    ensures |Keys| == 0;
  {
    Keys := [];
    Values := [];
    Repr := {this};
    head := null;
    nodes := [null];
  }

  method Find(key: Key) returns (present: bool, val: Value)
    requires Valid();
    ensures !present ==> key !in Keys;
    ensures present ==> (exists i :: 0 <= i && i < |Keys| && Keys[i] == key && Values[i] == val);
  {
    var p, n, prev := FindIndex(key);
    if (p == null) {
      present := false;
    } else {
      val := p.val;
      present := true;
    }
  }

  method Add(key: Key, val: Value)
    requires Valid();
    modifies Repr;
    ensures Valid() && fresh(Repr - old(Repr));
    ensures (forall i :: 0 <= i && i < |old(Keys)| && old(Keys)[i] == key ==>
                |Keys| == |old(Keys)| &&
                Keys[i] == key && Values[i] == val &&
                (forall j :: 0 <= j && j < |Values| && i != j ==>
                    Keys[j] == old(Keys)[j] && Values[j] == old(Values)[j]));
    ensures key !in old(Keys) ==> Keys == [key] + old(Keys) && Values == [val] + old(Values);
  {
    var p, n, prev := FindIndex(key);
    if (p == null) {
      var h := new Node<Key,Value>;
      h.key := key;  h.val := val;  h.next := head;
      head := h;
      Keys := [key] + Keys;  Values := [val] + Values;
      nodes := [h] + nodes;
      Repr := Repr + {h};
    } else {
      p.val := val;
      Values := Values[n := val];
    }
  }

  method Remove(key: Key)// returns (ghost h: int)
    requires Valid();
    modifies Repr;
    ensures Valid() && fresh(Repr - old(Repr));
    // no key is introduced:
    ensures (forall k :: k in Keys ==> k in old(Keys));
    // at most one key is removed:
    ensures (forall k :: k in old(Keys) ==> k in Keys || k == key);
    // other values don't change:
    ensures key !in old(Keys) ==> Keys == old(Keys) && Values == old(Values);
    ensures key in old(Keys) ==>
            |Keys| == |old(Keys)| - 1 && key !in Keys &&
            (exists h ::
              0 <= h && h < |old(Keys)| &&
              Keys[..h] == old(Keys)[..h] &&
              Values[..h] == old(Values)[..h] &&
              Keys[h..] == old(Keys)[h+1..] &&
              Values[h..] == old(Values)[h+1..]);
  {
    var p, n, prev := FindIndex(key);
    if (p != null) {
      Keys := Keys[..n] + Keys[n+1..];
      Values := Values[..n] + Values[n+1..];
      assert Keys[n..] == old(Keys)[n+1..];
      assert Values[n..] == old(Values)[n+1..];

      nodes := nodes[..n] + nodes[n+1..];
      if (prev == null) {
        head := head.next;
      } else {
        prev.next := p.next;
      }
    }
  }

  /*private*/ method FindIndex(key: Key) returns (p: Node<Key,Value>, ghost n: int, prev: Node<Key,Value>)
    requires Valid();
    ensures p == null ==> key !in Keys;
    ensures p != null ==>
              0 <= n && n < |Keys| && Keys[n] == key &&
              key !in Keys[..n] && key !in Keys[n+1..] &&
              p == nodes[n] &&
              ((n == 0 && prev == null) || (0 < n && prev == nodes[n-1]));
  {
    n := 0;
    prev := null;
    p := head;
    while (p != null)
      invariant n <= |Keys| && p == nodes[n];
      invariant key !in Keys[..n];
      invariant (n == 0 && prev == null) || (0 < n && prev == nodes[n-1]);
      decreases |Keys| - n;
    {
      if (p.key == key) {
        return;
      } else {
        n := n + 1;
        prev := p;
        p := p.next;
      }
    }
  }
}

class Node<Key,Value> {
  var key: Key;
  var val: Value;
  var next: Node<Key,Value>;
}
