// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Note: We are using the built-in equality to compare keys.
//
// The implementation uses a linked list, which isn't the most efficient
// representation of a dictionary.  However, for the benchmark, it shows
// that the specification can use mathematical sequences while the
// implementation uses a linked list.

class Map<Key(==),Value> {
  ghost var M: map<Key,Value>
  ghost var Repr: set<object>

  var head: Node?<Key,Value>
  ghost var Spine: set<Node<Key,Value>>

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr && Spine <= Repr &&
    SpineValid(Spine, head) &&
    (forall k :: k in M ==> exists n :: n in Spine && n.key == k) &&
    (forall n :: n in Spine ==> n.key in M && n.val == M[n.key]) &&
    (forall n,n' :: n in Spine && n' in Spine && n != n' ==> n.key != n'.key) &&
    (forall n :: n in Spine ==> n.next != head) &&
    (forall n,n' :: n in Spine && n' in Spine && n.next == n'.next ==> n == n')
  }
  static ghost predicate SpineValid(spine: set<Node<Key,Value>>, n: Node?<Key,Value>)
    reads spine
  {
    (n == null && spine == {}) ||
    (n != null && n in spine && n.Spine == spine - {n} && SpineValid(n.Spine, n.next))
  }
  static ghost predicate SpineValid_One(spine: set<Node<Key,Value>>, n: Node?<Key,Value>)
    reads spine
  {
    (n == null && spine == {}) ||
    (n != null && n in spine && n.Spine == spine - {n})
  }
  lemma SpineValidSplit(spine: set<Node<Key,Value>>, p: Node?<Key,Value>)
    requires SpineValid(spine, p)
    ensures SpineValid_One(spine, p)
    ensures forall n :: n in spine ==> SpineValid_One(n.Spine, n.next)
    ensures forall n :: n in spine ==> n.next == null || n.next in spine
  {
  }
  lemma SpineValidCombine(spine: set<Node<Key,Value>>, p: Node?<Key,Value>)
    requires SpineValid_One(spine, p)
    requires forall n :: n in spine ==> SpineValid_One(n.Spine, n.next)
    ensures SpineValid(spine, p)
  {
  }


  constructor Init()
    ensures Valid() && fresh(Repr)
    ensures M == map[]
  {
    head, Spine := null, {};
    M, Repr := map[], {this};
  }

  /*private*/ method FindIndex(key: Key) returns (prev: Node?<Key,Value>, p: Node?<Key,Value>)
    requires Valid()
    ensures p == null ==> key !in M
    ensures p != null ==>
              key in M &&
              p in Spine && p.key == key &&
              (p == head ==> prev == null) &&
              (p != head ==> prev in Spine && prev.next == p)
  {
    prev, p := null, head;
    ghost var spine := Spine;
    while p != null
      invariant SpineValid(spine, p)
      invariant p != null ==> p in spine
      invariant p == head ==> prev == null
      invariant p != head ==> prev in Spine && prev.next == p && head !in spine
      invariant key in M ==> exists n :: n in spine && n.key == key;
      decreases spine
    {
      if p.key == key {
        return;
      } else {
        spine := p.Spine;
        prev, p := p, p.next;
      }
    }
  }

  method Find(key: Key) returns (result: Maybe<Value>)
    requires Valid()
    ensures result == None ==> key !in M
    ensures result.Some? ==> key in M && result.get == M[key]
  {
    var prev, p := FindIndex(key);
    if p == null {
      result := None;
    } else {
      result := Some(p.val);
    }
  }

  // If key is not already in M, add [key := val].
  // If key is already in M, change M[key] to val.
  method Add(key: Key, val: Value)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures M == old(M)[key := val]
  {
    var prev, p := FindIndex(key);
    if p == null {
      var h := new Node(key, val);
      h.next, h.Spine := head, Spine;
      head, Spine, Repr := h, Spine + {h}, Repr + {h};
      M := M[key := val];
    } else {
      p.val := val;
      M := M[key := val];
      // prove that SpineValid(Spine, head) has not changed
      // TODO: This is wonderful, but how come this actually works?
      // NOTE: This is a place where a two-state lemma would be highly useful
      ghost var s', p' := Spine, head;
      while p' != null
        invariant old(allocated(p'))
        invariant old(SpineValid(s', p'))
        invariant old(SpineValid(Spine, head)) ==> SpineValid(Spine, head) || !SpineValid(s', p')
        decreases s'
      {
        s', p' := p'.Spine, p'.next;
      }
    }
  }

  // Removes key from the domain of M (and does nothing if key wasn't in M to begin with)
  method {:rlimit 3000} {:vcs_split_on_every_assert} Remove(key: Key)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures M == map k | k in old(M) && k != key :: old(M)[k]
  {
    var prev, p := FindIndex(key);
    if p != null {
      if prev == null {
        RemoveFirst(key, p);
      } else {
        RemoveNonFirst(key, prev, p);
      }
    }
  }

  /*private*/ method RemoveFirst(key: Key, p: Node<Key,Value>)
    requires Valid()
    requires key in M && p == head
    requires p in Spine && p.key == key
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures M == map k | k in old(M) && k != key :: old(M)[k]
  {
    Spine, head := head.Spine, head.next;
    M := map k | k in M && k != key :: M[k];
    forall k | k in M
      ensures exists n :: n in Spine && n.key == k
    {
      if k != key {
        assert k in old(M);
        var n :| n in old(Spine) && old(n.key) == k;
        assert n.key == old(n.key);
      }
    }
  }

  /*private*/ method RemoveNonFirst(key: Key, prev: Node<Key,Value>, p: Node<Key,Value>)
    requires Valid()
    requires key in M && p != head
    requires p in Spine && p.key == key
    requires prev in Spine && prev.next == p
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures M == map k | k in old(M) && k != key :: old(M)[k]

  {
    SpineValidSplit(Spine, head);

    prev.next := p.next;
    forall n | n in Spine {
      n.Spine := n.Spine - {p};
    }
    Spine := Spine - {p};
    M := map k | k in M && k != key :: M[k];

    forall k | k in M
      ensures exists n :: n in Spine && n.key == k
    {
      assert k in old(M) && k != key;
      var n :| n in old(Spine) && old(n.key) == k;
      assert n.key == old(n.key);
    }

    assert SpineValid(Spine, head) by {
      SpineValidCombine(Spine, head);
    }
  }

}

class Node<Key,Value> {
  var key: Key
  var val: Value
  var next: Node?<Key,Value>
  ghost var Spine: set<Node<Key,Value>>

  constructor (key: Key, val: Value)
    ensures this.key == key && this.val == val
  {
    this.key, this.val := key, val;
  }
}

datatype Maybe<T> = None | Some(get: T)
