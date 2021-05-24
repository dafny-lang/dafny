// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Dt = Dt(x:int)
{
  method {:timeLimitMultiplier 5} Test(y:int) {
    var z := y;
    assert z == y;
  }
}

