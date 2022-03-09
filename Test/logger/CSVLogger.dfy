// RUN: %dafny /verificationLogger:csv;LogFileName="%t.csv" "%s"
// RUN: %OutputCheck --file-to-check "%t.csv" "%s"

// CHECK: TestResult\.DisplayName,TestResult\.Outcome,TestResult\.Duration,TestResult\.ResourceCount
// CHECK-NEXT: Impl\$\$_module.__default\.ExampleWithSplits\$\$1,Passed,.*,.*

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
