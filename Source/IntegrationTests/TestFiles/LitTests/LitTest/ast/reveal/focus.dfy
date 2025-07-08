// RUN: %verify --type-system-refresh --allow-axioms --isolate-assertions %s > %t
// RUN: %diff "%s.expect" "%t"

method doFocus1(x: bool) returns (y: int) {
  y := 1;                     // Batch 1    Batch 2
  assert y == 1;              // Assertion  --
  if x {
    if false {
      assert y >= 0;          // --         Assertion
      assert {:focus} y <= 2; // --         Assertion
      y := 2;
      assert y == 2;          // --         Assertion
    }
  } else {
    assert y == 1;            // Assertion  --
  }
  assert y == 1;              // Assertion  Assertion
  if !x {
    assert y >= 1;            // Assertion  Assertion
  } else {
    assert y <= 1;            // Assertion  Assertion
  }
}

method doFocus2(x: bool) returns (y: int) {
  y := 1;                     // Batch 1    Batch 2
  assert y == 1;              // Assertion  --
  if x {
    while false {
      assert y >= 0;          // --         Assertion
      assert {:focus} y <= 2; // --         Assertion
      y := 2;
      assert y == 2;          // --         Assertion
    }
  } else {
    assert y == 1;            // Assertion  --
  }
  assert y == 1;              // Assertion  --
  if !x {
    assert y >= 1;            // Assertion  --
  } else {
    assert y <= 1;            // Assertion  --
  }
}