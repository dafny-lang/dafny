// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Edited B6 to include GetChar and PutChar

//This is the Queue from Benchmark 3.

//restriction:we assume streams are finite
//what else can we specify?


class Queue<T> {
  var contents: seq<T>;
  method Init()
    modifies this;
    ensures |contents| == 0;
  method Enqueue(x: T)
    modifies this;
    ensures contents == old(contents) + [x];
  method Dequeue() returns (x: T)
    requires 0 < |contents|;
    modifies this;
    ensures contents == old(contents)[1..] && x == old(contents)[0];
  ghost function Head(): T
    requires 0 < |contents|;
    reads this;
  { contents[0] }
  ghost function Get(i: int): T
    requires 0 <= i < |contents|;
    reads this;
  { contents[i] }
}

class Stream {
  ghost var footprint:set<object>;
  var stream:seq<int>;
  var isOpen:bool;

  ghost function Valid():bool
    reads this, footprint;
  {
    this in footprint && isOpen
  }

  method GetCount() returns (c:int)
    requires Valid();
    ensures 0 <= c;
  {
    c := |stream|;
  }

  method Create() //writing
    modifies this;
    ensures Valid() && fresh(footprint - {this});
    ensures stream == [];
  {
    stream := [];
    footprint := {this};
    isOpen := true;
  }

  method Open() //reading
    modifies this;
    ensures Valid() && fresh(footprint - {this});
  {
    footprint := {this};
    isOpen := true;
  }

  method PutChar(x:int )
    requires Valid();
    modifies footprint;
    ensures Valid() && fresh(footprint - old(footprint));
    ensures stream == old(stream) + [x];
  {
    stream:= stream + [x];
  }

  method GetChar()returns(x:int)
    requires Valid() && 0 < |stream|;
    modifies footprint;
    ensures Valid() && fresh(footprint - old(footprint));
    ensures x ==old(stream)[0];
    ensures stream == old(stream)[1..];
  {
    x := stream[0];
    stream := stream[1..];
  }

  method AtEndOfStream() returns(eos:bool)
    requires Valid();
    ensures eos  <==> |stream| == 0;
  {
    eos := |stream| == 0;
  }

  method Close()
    requires Valid();
    modifies footprint;
  {
    isOpen := false;
  }
}


class Client {
  method Sort(q: Queue<int>) returns (r: Queue<int>)
    modifies q;
    ensures fresh(r);
    ensures |r.contents| == |old(q.contents)|;
    ensures forall i, j :: 0 <= i < j < |r.contents| ==> r.Get(i) <= r.Get(j);
    // the final Queue is a permutation of the input Queue
    ensures multiset(r.contents) == multiset(old(q.contents));

  method Main()
  {
    var rd := new Stream;
    rd.Open();

    var q := new Queue<int>;
    while (true)
      invariant rd.Valid() && fresh(rd.footprint) && fresh(q);
      decreases |rd.stream|;
    {
      var eos := rd.AtEndOfStream();
      if (eos) {
        break;
      }

      var ch := rd.GetChar();
      q.Enqueue(ch);
    }

    rd.Close();
    q := Sort(q);

    var wr := new Stream;
    wr.Create();
    while (0 < |q.contents|)
      invariant wr.Valid() && fresh(wr.footprint) && fresh(q) && q !in wr.footprint;
    {
      var ch := q.Dequeue();
      wr.PutChar(ch);
    }
    wr.Close();
  }
}
