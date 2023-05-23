// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class {:autocontracts} RingBuffer<T(0)>
{
  // public view of the class:
  ghost var Contents: seq<T>  // the contents of the ring buffer
  ghost var N: nat  // the capacity of the ring buffer

  // private implementation:
  var data: array<T>
  var start: nat
  var len: nat

  // Valid encodes the consistency of RingBuffer objects (think, invariant)
  ghost predicate Valid()
  {
    data.Length == N &&
    (N == 0 ==> len == start == 0 && Contents == []) &&
    (N != 0 ==> len <= N && start < N) &&
    Contents == if start + len <= N then data[start..start+len]
                                    else data[start..] + data[..start+len-N]
  }

  constructor Create(n: nat)
    ensures Contents == [] && N == n
  {
    data := new T[n];
    start, len := 0, 0;
    Contents, N := [], n;
  }

  method Clear()
    ensures Contents == [] && N == old(N)
  {
    len := 0;
    Contents := [];
  }

  method Head() returns (x: T)
    requires Contents != [];
    ensures x == Contents[0]
  {
    x := data[start];
  }

  method Enqueue(x: T)
    requires |Contents| != N
    ensures Contents == old(Contents) + [x] && N == old(N)
  {
    var nextEmpty := if start + len < data.Length
                     then start + len else start + len - data.Length;
    data[nextEmpty] := x;
    len := len + 1;
    Contents := Contents + [x];
  }

  method ResizingEnqueue(x: T)
    ensures Contents == old(Contents) + [x] && N >= old(N)
  {
    if data.Length == len {
      var more := data.Length + 1;
      var d := new T[data.Length + more];
      forall i | 0 <= i < data.Length {
        d[if i < start then i else i + more] := data[i];
      }
      N, data, start := N + more, d, if len == 0 then 0 else start + more;
    }
    var nextEmpty := if start + len < data.Length
                     then start + len else start + len - data.Length;
    data[nextEmpty] := x;
    len := len + 1;
    Contents := Contents + [x];
  }

  method Dequeue() returns (x: T)
    requires Contents != []
    ensures x == old(Contents)[0] && Contents == old(Contents)[1..] && N == old(N)
  {
    x := data[start];  assert x == Contents[0];
    start, len := if start + 1 == data.Length then 0 else start + 1, len - 1;
    Contents := Contents[1..];
  }
}

method TestHarness(x: int, y: int, z: int)
{
  var b := new RingBuffer.Create(2);
  b.Enqueue(x);
  b.Enqueue(y);
  var h := b.Dequeue();  assert h == x;
  b.Enqueue(z);
  h := b.Dequeue();  assert h == y;
  h := b.Dequeue();  assert h == z;
}
