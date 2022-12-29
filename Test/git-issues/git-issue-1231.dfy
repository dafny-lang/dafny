// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Dt = Dt(x:int)
{
  method {:timeLimitMultiplier 5} DatatypeTest(y:int) {
    var z := y;
    assert z == y;
  }
}

newtype Even = x : int | x % 2 == 0
{
  method {:timeLimitMultiplier 4} NewtypeTest(y:int) {
    assert y == y;
  }
}

codatatype Stream<T> = More(head: T, rest: Stream) 
{
  method {:timeLimitMultiplier 3} CodatatypeTest(y:int) {
    assert y == y;
  }
}
