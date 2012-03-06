class {:autocontracts} RingBuffer<T>
{
  // public fields that are used to define the abstraction:
  ghost var Contents: seq<T>;  // the contents of the ring buffer
  ghost var N: nat;  // the capacity of the ring buffer

  // Valid encodes the consistency of RingBuffer objects (think, invariant).
  // An explanation of this idiom is explained in the README file.
  predicate Valid
  {
    data != null &&
    data.Length == N &&
    (N == 0 ==> len == first == 0 && Contents == []) &&
    (N != 0 ==> len <= N && first < N) &&
    Contents == if first + len <= N then data[first..first+len] 
                                    else data[first..] + data[..first+len-N]
  }

  // private implementation:
  var data: array<T>;
  var first: nat;
  var len: nat;

  constructor Create(n: nat)
    ensures Contents == [] && N == n;
  {
    data := new T[n];
    first, len := 0, 0;
    Contents, N := [], n;
  }

  method Clear()
    ensures Contents == [] && N == old(N);
  {
    len := 0;
    Contents := [];
  }

  method Head() returns (x: T)
    requires Contents != [];
    ensures x == Contents[0];
  {
    x := data[first];
  }

  method Push(x: T)
    requires |Contents| != N;
    ensures Contents == old(Contents) + [x] && N == old(N);
  {
    var nextEmpty := if first + len < data.Length 
                     then first + len else first + len - data.Length;
    data[nextEmpty] := x;
    len := len + 1;
    Contents := Contents + [x];
  }

  method Pop() returns (x: T)
    requires Contents != [];
    ensures x == old(Contents)[0] && Contents == old(Contents)[1..] && N == old(N);
  {
    x := data[first];
    first, len := if first + 1 == data.Length then 0 else first + 1, len - 1;
    Contents := Contents[1..];
  }
}

method TestHarness(x: int, y: int, z: int)
{
  var b := new RingBuffer<int>.Create(2);
  b.Push(x);
  b.Push(y);
  var h := b.Pop();  assert h == x;
  b.Push(z);
  h := b.Pop();  assert h == y;
  h := b.Pop();  assert h == z;
}
