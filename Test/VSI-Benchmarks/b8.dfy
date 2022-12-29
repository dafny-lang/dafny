// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Benchmark 8

// A dictionary is a mapping between words and sequences of words
// to set up the dictionary in main we will read a stream of words and put them into the mapping - the first element of the stream is the term,
// the following words (until we read null) form the terms definition. Then the stream provides the next term etc.

datatype Maybe<T> = None | Some(get: T)

class Queue<T> {
  var contents: seq<T>
  constructor Init()
    ensures |contents| == 0
  method Enqueue(x: T)
    modifies this
    ensures contents == old(contents) + [x]
  method Dequeue() returns (x: T)
    requires 0 < |contents|
    modifies this
    ensures contents == old(contents)[1..] && x == old(contents)[0]
  function method Head(): T
    requires 0 < |contents|
    reads this
  { contents[0] }
  function method Get(i: int): T
    requires 0 <= i < |contents|
    reads this
  { contents[i] }
}


class Glossary {
  method Sort(q: Queue<Word>) returns (r: Queue<Word>)
    modifies q
    ensures fresh(r)
    ensures |r.contents| == |old(q.contents)|
    ensures forall i, j :: 0 <= i && i < j && j < |r.contents| ==>
               r.Get(i).AtMost(r.Get(j))
    // the final Queue is a permutation of the input Queue
    ensures multiset(r.contents) == multiset(old(q.contents))

  method Main()
    decreases *  // this Main method may run forever
  {
    var rs:= new ReaderStream;
    rs.Open();
    var glossary := new Map<Word,seq<Word>>.Init();
    var q:Queue<Word> := new Queue<Word>.Init();

    while true
      invariant rs.Valid() && fresh(rs.footprint)
      invariant glossary.Valid()
      invariant glossary !in rs.footprint
      invariant q !in rs.footprint
      invariant q.contents == glossary.keys
      decreases *  // we leave out the decreases clause - unbounded stream
    {
      var term, definition := readDefinition(rs);
      if term == null {
        break;
      }
      var r := glossary.Find(term);
      if r == None {
        glossary.Add(term, definition);
        q.Enqueue(term);
      }
    }

    rs.Close();
    ghost var qc := q.contents;
    q := Sort(q);
    assert forall k :: k in q.contents ==> k in multiset(q.contents);
    var wr := new WriterStream;
    wr.Create();

    while 0 < |q.contents|
      invariant wr.Valid() && fresh(wr.footprint)
      invariant glossary.Valid()
      invariant glossary !in wr.footprint
      invariant q !in wr.footprint
      invariant forall k :: k in q.contents ==> k in glossary.keys
    {
      var term := q.Dequeue();
      var r := glossary.Find(term);
      assert r.Some?;
      var definition := r.get;

      // write term with a html anchor
      wr.PutWordInsideTag(term, term);
      var i := 0;

      var qcon := q.contents;
      while i < |definition|
        invariant wr.Valid() && fresh(wr.footprint)
        invariant glossary.Valid()
        invariant glossary !in wr.footprint
        invariant q !in wr.footprint
        invariant qcon == q.contents
        invariant forall k :: k in q.contents ==> k in glossary.keys
      {
        var w := definition[i];
        var r := glossary.Find(w);
        if r == None {
          wr.PutWordInsideHyperlink(w, w);
        } else {
          wr.PutWord(w);
        }
        i:= i +1;
      }
    }
    wr.Close();
  }


  method readDefinition(rs:ReaderStream) returns (term:Word?, definition:seq<Word?>)
    requires rs.Valid()
    modifies rs.footprint
    ensures rs.Valid() && fresh(rs.footprint - old(rs.footprint))
    ensures term != null ==> null !in definition
    decreases *  // this method may run forever
  {
    term := rs.GetWord();
    if term != null {
      definition := [];
      while true
        invariant rs.Valid() && fresh(rs.footprint - old(rs.footprint))
        invariant null !in definition
        decreases *  // we leave out the decreases clause - unbounded stream
      {
        var w := rs.GetWord();
        if w == null {
          break;
        }
        definition := definition + [w];
      }
    }
  }
}

class Word
{
  predicate AtMost(w: Word)
}

class ReaderStream {
  ghost var footprint: set<object>
  var isOpen: bool

  predicate Valid()
    reads this, footprint
  {
    this in footprint && isOpen
  }

  method Open() //reading
    modifies this
    ensures Valid() && fresh(footprint -{this})
  {
    footprint := {this};
    isOpen :=true;
  }

  method GetWord() returns (x: Word?)
    requires Valid()
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
  {
  }

  method Close()
    requires Valid()
    modifies footprint
  {
    isOpen := false;
  }
}

class WriterStream {
  ghost var footprint:set<object>
  var stream:seq<int>
  var isOpen:bool

  predicate Valid()
    reads this, footprint
  {
    this in footprint && isOpen
  }

  method Create() //writing
    modifies this
    ensures Valid() && fresh(footprint -{this})
    ensures stream == []
  {
    stream := [];
    footprint := {this};
    isOpen:= true;
  }
  method GetCount() returns (c:int)
    requires Valid()
    ensures 0 <= c
  {
    c:=|stream|;
  }

  method PutWord(w:Word )
    requires Valid()
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures old(stream) <= stream
  {
  }

  method PutWordInsideTag(tag:Word,w:Word )
    requires Valid()
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures old(stream) <= stream
  {
  }

  method PutWordInsideHyperlink(tag:Word, w:Word)
    requires Valid()
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures old(stream) <= stream
  {
  }

  method Close()
    requires Valid()
    modifies footprint
  {
    isOpen := false;
  }
}




class Map<Key(==),Value> {
  var keys: seq<Key>
  var values: seq<Value>

  predicate Valid()
    reads this
  {
    |keys| == |values| &&
    forall i, j :: 0 <= i < j < |keys| ==> keys[i] != keys[j]
  }

  method Init()
    modifies this
    ensures Valid() && |keys| == 0
  {
    keys := [];
    values := [];
  }

  method Find(key: Key) returns (result: Maybe<Value>)
    requires Valid()
    ensures result == None ==> key !in keys
    ensures result.Some? ==> exists i :: 0 <= i < |keys| && keys[i] == key && values[i] == result.get
  {
    var j := FindIndex(key);
    if j == -1 {
      return None;
    } else {
      return Some(values[j]);
    }
  }

  method Add(key: Key, val: Value)
    requires Valid()
    modifies this
    ensures Valid()
    ensures forall i :: 0 <= i < |old(keys)| && old(keys)[i] == key ==>
              |keys| == |old(keys)| &&
              keys[i] == key && values[i] == val &&
              forall j :: 0 <= j < |values| && i != j ==> keys[j] == old(keys)[j] && values[j] == old(values)[j]
    ensures key !in old(keys) ==> keys == old(keys) + [key] && values == old(values) + [val]
  {
    var j := FindIndex(key);
    if j == -1 {
      keys := keys + [key];
      values := values + [val];
    } else {
      values := values[j := val];
    }
  }

  method Remove(key: Key)
    requires Valid()
    modifies this
    ensures Valid()
    // no key is introduced:
    ensures (forall k :: k in keys ==> k in old(keys))
    // at most one key is removed:
    ensures forall k :: k in old(keys) ==> k in keys || k == key
    // the given key is not there:
    // other values don't change:
    ensures key !in old(keys) ==> keys == old(keys) && values == old(values)
    ensures key in old(keys) ==>
            |keys| == |old(keys)| - 1 && key !in keys &&
            exists h ::
              0 <= h <= |keys| &&
              keys[..h] == old(keys)[..h] &&
              values[..h] == old(values)[..h] &&
              keys[h..] == old(keys)[h+1..] &&
              values[h..] == old(values)[h+1..]
  {
    var j := FindIndex(key);
    if 0 <= j {
      keys := keys[..j] + keys[j+1..];
      values := values[..j] + values[j+1..];
    }
  }

  method FindIndex(key: Key) returns (idx: int)
    requires Valid()
    ensures -1 <= idx && idx < |keys|
    ensures idx == -1 ==> key !in keys
    ensures 0 <= idx ==> keys[idx] == key
  {
    var j := 0;
    while j < |keys|
      invariant j <= |keys|
      invariant key !in keys[..j]
    {
      if keys[j] == key {
        idx := j;
        return;
      }
      j := j + 1;
    }
    idx := -1;
  }
}
