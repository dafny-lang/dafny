// Regression test that just ensures this runs without errors.
// Inspecting the output is dependent on implementing %OutputCheck.
// See https://github.com/dafny-lang/dafny/issues/1640.

// RUN: %dafny /verificationLogger:trx "%s"

method ExampleWithSplits() returns (y: int)
  ensures y >= 0
{
  var x: int;
  x := 5;
  y := 0;
  while (x > 0)
    invariant x + y == 5
    invariant x*x <= 25
  {
    x := x - 1;
    assert {:split_here} (x+y) * (x+y) > 25;
    y := y + 1;
    if (x < 3) {
      assert 2 < 2;
      assert {:split_here} y*y > 4;
    }
    else {
      assert {:split_here} y*y*y < 8;
      assert 2 < 2;
    }
    assert {:split_here} (x+y) * (x+y) == 25;
  }
}

method ExampleWithoutSplits() {
  assert 1 + 1 == 2;
  assert 2 + 2 == 4;
  assert 3 + 3 == 6;
}

method AnotherExampleWithoutSplits() {
  assert 1 + 1 == 2;
  assert 2 + 2 == 4;
  assert 3 + 3 == 6;
}
