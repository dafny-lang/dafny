// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

method Main()
{
  var z := OutParametersInLetBodies();
  DoSomeFloors();
}

// Here is a regression test

method OutParametersInLetBodies() returns (t: int)
{
  t := 25;
  var z := var y := 30; F(t, y);
  assert z == 55;
  print z, "\n";
}

function F(x: int, y: int): int { x + y }


// Here is another compiler test

method DoSomeFloors()
{
  P(-3.0, -3);
  P(-2.8, -3);
  P(-2.2, -3);
  P(-0.1, -1);
  P(0.0, 0);
  P(0.1, 0);
  P(2.2, 2);
  P(2.8, 2);
  P(3.0, 3);
}

method P(r: real, y: int)
  requires r.Floor == y
{
  var x := r.Floor;
  print "Trunc( ", r, " ) = ", x, " (expected ", y, ")\n";
}
