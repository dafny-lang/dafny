class Entry<K(==), V> {
  var hash: int
  var key: K
  var value: V
  var next: Entry?<K, V>
  ghost const Repr: set<object>

  constructor(hash: int, key: K, value: V, next: Entry?<K, V>)
    ensures next == null || this !in next.Repr
    ensures this.next == next && this.key == key && this.value == value
    ensures this.Repr == if next == null then {this} else {this} + next.Repr
    {
      this.hash := hash;
      this.key := key;
      this.value := value;
      this.next := next;
      this.Repr := if next == null then {this} else {this} + next.Repr;
    }

  function Count(): (res: nat)
    reads this, Repr
    decreases |Repr|
    requires Invariant()
  {
    1 + (if next == null then 0 else next.Count())
  }

  ghost predicate Invariant()
    reads this, Repr
    decreases |Repr|
  {
    && this in Repr
    && if this.next == null then true
       else
         && Repr == {this} + next.Repr
         && this !in next.Repr
         && next in Repr
         && next.Invariant()
  }
  twostate lemma InvariantDoesNotDependOnValue()
    requires old(Invariant())
    requires forall e <- Repr | (e is Entry<K, V>) :: e.next == old(e.next)
    ensures Invariant()
    decreases |Repr|
  {
    if next != null {
      next.InvariantDoesNotDependOnValue();
    }
  }

  // Ensures that the first entries override the last ones
  ghost function ToModel(): map<K, V> reads this, Repr
    requires Invariant()
    decreases |Repr|
  {
    var recMap := if next == null then map[] else next.ToModel();
    recMap[key := value]
  }
}

class Segment {
  var count: int
  constructor() {
      this.count := 0;
    }
}

class ConcurrentHashMap<K(==), V> {
  var entries: array<Entry?<K, V>>
  var segments: array<Segment>

  ghost var model: map<K, V>
  ghost var Repr: set<object>
  ghost function {:vcs_split_on_every_assert} {:rlimit 1000} ToModel(startIndex: nat): map<K, V> reads this
    reads this, Repr
    requires startIndex <= entries.Length
    requires Invariant()
    decreases entries.Length - startIndex
  {
    if startIndex >= entries.Length then map[] else
    var rec := ToModel(startIndex + 1);
    var entry := entries[startIndex];
    rec + (if entry == null then map[] else entries[startIndex].ToModel())
  }
  ghost predicate InvariantPerEntry0(entry: Entry?<K, V>)
    reads this
    reads entry
  {
    entry != null ==>
      && entry in Repr
      && entry.Repr <= Repr
      && this !in entry.Repr
      && entries !in entry.Repr
  }
  ghost predicate InvariantPerEntry1(entry: Entry?<K, V>)
    reads this
    reads entry
          reads if entry != null then entry.Repr else {}
    requires InvariantPerEntry0(entry)
  {
    entry != null ==> entry.Invariant()
  }
  ghost predicate Invariant()
    reads this, Repr
  {
    && this in Repr
    && entries in Repr
    && segments in Repr
    && entries.Length == segments.Length
    && entries.Length >= 1
    && (forall i: nat | 0 <= i < this.entries.Length ::
          && (entries[i] != null ==> entries[i] in Repr)
          && InvariantPerEntry0(entries[i])
          && InvariantPerEntry1(entries[i])
          && InvariantPerEntry2(i))
    && (forall i: nat, j: nat | i < entries.Length && j < entries.Length && i != j ::
          entries[i] == null || entries[j] == null ||
          entries[i].Repr !! entries[j].Repr)
  }
  ghost predicate InvariantPerEntry2(i: int)
    reads this, entries, segments, Repr
    requires entries.Length == segments.Length
    requires 0 <= i < segments.Length
    requires InvariantPerEntry0(entries[i])
    requires InvariantPerEntry1(entries[i])
  {
    segments[i] in Repr &&
    if entries[i] != null then
      && segments !in entries[i].Repr
      && segments[i].count == entries[i].Count()
      && (forall j | 0 <= j < segments.Length :: segments[j] !in entries[i].Repr)
    else
      && segments[i].count == 0
  }

  function Hash(k: K): int // Needs to be given!

  method /*{:only}*/ {:vcs_split_on_every_assert} {:rlimit 3000} Put(k: K, v: V) returns (oldValueIfExisted: V)
    requires Invariant()
    modifies Repr
    ensures Invariant()
    {
      var hash := Hash(k);
      var indexEntry := hash % entries.Length;
      var e := entries[indexEntry];
      assert InvariantPerEntry1(entries[indexEntry]);
      assert e != null ==> e in Repr;
      while(e != null)
        invariant Invariant()
        invariant e != null ==> e in Repr && e.Invariant() && e.Repr <= Repr
        decreases if e == null then 0 else e.Count()
      {
        if e.hash == hash && k == e.key { // if key already exist means updating the value
          var oldValue := e.value;
          assert Invariant();
          label before:
          e.value := v;
          assert Invariant() by {
            e.InvariantDoesNotDependOnValue@before();
            forall i: nat | 0 <= i < this.entries.Length ensures
                && (entries[i] != null ==> entries[i] in Repr)
                && InvariantPerEntry0(entries[i])
                && InvariantPerEntry1(entries[i])
                && InvariantPerEntry2(i) {

            }
          }
          return oldValue;
        }
        e := e.next;
      }
      ghost var oldHead := entries[indexEntry];
      var newEntry := new Entry(hash, k, v, entries[indexEntry]);
      assert newEntry !in Repr;
      Repr := {newEntry} + Repr;
      assert newEntry.next != null ==> newEntry.next.Invariant();
      assert /*{:only} */&& newEntry in Repr
                         && newEntry.Repr <= Repr
                         && newEntry.Invariant();
      assert this as object != entries as object;
      assert this as object != segments as object;
      entries[indexEntry] := newEntry;
      segments[indexEntry].count := segments[indexEntry].count + 1;

      assert Invariant() by {
        assert forall i: nat | 0 <= i < this.entries.Length ::
            InvariantPerEntry1(entries[i]) by {
          forall i: nat | 0 <= i < this.entries.Length ensures
              InvariantPerEntry1(entries[i]) {
            if i == indexEntry {
              assert InvariantPerEntry1(entries[i]);
            } else {
              assert InvariantPerEntry1(entries[i]);
            }
          }
        }
      }
      return v;
    }
}
