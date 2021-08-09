// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function RecursiveFrame(y: int): set<object>
  reads if 0 < y then RecursiveFrame(y - 1) else {} // BOGUS: would be nice if this verified
  decreases y
{
  {}
}

function MyFrame(y: int, o: object, p: object): set<object>
  reads o
{
  {o, p}
}

trait T {
  function F(y: nat): int
    ensures F(y) < 10
  function H(y: nat): int
    ensures H(y) == 0
  function H'(y: nat): int
    ensures H'(y) == 0
  function H''(y: nat): int
    ensures H''(y) == 0
  function R(o: object, p: object): int
    reads MyFrame(0, o, p)
    decreases 0
}

function MyFrame'(y: int, o: object, p: object): set<object>
  reads o
{
  {o, p}
}

class D extends T {
  function F(y: int): int
    ensures true // BOGUS: should not verify
  {
    3
  }

  function H(y: nat): int
    ensures H(y) == if y == 0 then 0 else H(y - 1) // BOGUS: should verify
  function H'(y: nat): int
    ensures H'(y) == if y == 0 then 0 else (this as T).H'(y - 1) // BOGUS: should verify
  function H''(y: nat): int
    ensures (this as T).H''(y) == if y == 0 then 0 else H''(y - 1) // error: call to T.H'' does not terminate
  function R(o: object, p: object): int
    reads MyFrame'(0, o, o)
    decreases 0
}
