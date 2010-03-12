// Note: We are using the built-in equality to compare keys.
// Note: Our specifications are rather tied to the implementation.  In
// particular, we use indices into .keys and .values.  Nicer would
// be if Dafny had a built-in map type that could be used in specifications.
// Or, perhaps inductive data types could be used in specifications,
// if Dafny had those.

class Map<Key,Value> {
  var keys: seq<Key>;
  var values: seq<Value>;

  function Valid(): bool
    reads this;
  {
    |keys| == |values| &&
    (forall i, j :: 0 <= i && i < j && j < |keys| ==> keys[i] != keys[j])
  }

  method Init()
    modifies this;
    ensures Valid() && |keys| == 0;
  {
    keys := [];
    values := [];
  }

  method Find(key: Key) returns (present: bool, val: Value)
    requires Valid();
    ensures !present ==> key !in keys;
    ensures present ==> (exists i :: 0 <= i && i < |keys| &&
                                     keys[i] == key && values[i] == val);
  {
    call j := FindIndex(key);
    if (j == -1) {
      present := false;
    } else {
      present := true;
      val := values[j];
    }
  }

  method Add(key: Key, val: Value)
    requires Valid();
    modifies this;
    ensures Valid();
    ensures (forall i :: 0 <= i && i < |old(keys)| && old(keys)[i] == key ==>
              |keys| == |old(keys)| &&
              keys[i] == key && values[i] == val &&
              (forall j :: 0 <= j && j < |values| && i != j ==> keys[j] == old(keys)[j] && values[j] == old(values)[j]));
    ensures key !in old(keys) ==> keys == old(keys) + [key] && values == old(values) + [val];
  {
    call j := FindIndex(key);
    if (j == -1) {
      keys := keys + [key];
      values := values + [val];
    } else {
      values := values[j := val];
    }
  }

  method Remove(key: Key)
    requires Valid();
    modifies this;
    ensures Valid();
    // no key is introduced:
    ensures (forall k :: k in keys ==> k in old(keys));
    // at most one key is removed:
    ensures (forall k :: k in old(keys) ==> k in keys || k == key);
    // the given key is not there:
    // other values don't change:
    ensures key !in old(keys) ==> keys == old(keys) && values == old(values);
    ensures key in old(keys) ==>
            |keys| == |old(keys)| - 1 && key !in keys &&
            (exists h ::
              0 <= h && h <= |keys| &&
              keys[..h] == old(keys)[..h] &&
              values[..h] == old(values)[..h] &&
              keys[h..] == old(keys)[h+1..] &&
              values[h..] == old(values)[h+1..]);
  {
    call j := FindIndex(key);
    if (0 <= j) {
      keys := keys[..j] + keys[j+1..];
      values := values[..j] + values[j+1..];
    }
  }

  method FindIndex(key: Key) returns (idx: int)
    requires Valid();
    ensures -1 <= idx && idx < |keys|;
    ensures idx == -1 ==> key !in keys;
    ensures 0 <= idx ==> keys[idx] == key;
  {
    var j := 0;
    while (j < |keys|)
      invariant j <= |keys|;
      invariant key !in keys[..j];
      decreases |keys| -j;
    {
      if (keys[j] == key) {
        idx := j;
        return;
      }
      j := j + 1;
    }
    idx := -1;
  }
}
