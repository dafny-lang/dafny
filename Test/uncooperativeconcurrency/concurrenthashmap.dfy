class Entry<K(==), V> {
  var hash: int
  var key: K
  var value: V
  var next: Entry?<K, V>
  ghost const Repr: set<object>

  constructor(hash: int, key: K, value: V, next: Entry?<K, V>)
    ensures next == null || this !in next.Repr;
    {
      this.hash := hash;
      this.key := key;
      this.value := value;
      this.Repr := if next == null then {this} else {this} + next.Repr;
    }

  ghost predicate Invariant()
    reads this, Repr
  {
    && this in Repr
    && if this.next == null then true
       else
         && next.Repr == {this} + Repr
         && this !in next.Repr
         && next.Invariant()
  }

  // Ensures that the first entries override the last ones
  function ToModel(): map<K, V> reads this, Repr
    requires Invariant()
    decreases |Repr|
  {
    var recMap := if next == null then map[] else next.ToModel();
    recMap[key := value]
  }
}

class ConcurrentHashMap<K(==), V> {
  var entries: array<Entry?<K, V>>
  ghost var model: map<K, V>
  ghost var Repr: set<object>
  function {:vcs_split_on_every_assert} {:rlimit 1000} ToModel(startIndex: nat): map<K, V> reads this
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
  ghost predicate Invariant()
    reads this, Repr
  {
    && this in Repr
    && entries in Repr
    && (forall i: nat | 0 <= i < this.entries.Length ::
          entries[i] != null ==>
            && entries[i] in Repr
            && entries[i].Repr <= Repr
            && entries[i].Invariant())
  }
}
