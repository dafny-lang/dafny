// RUN: %testDafnyForEachResolver "%s" -- --allow-warnings


ghost function AnotherBrokenFunction(): nat {
  var y := 0;
  assert true by {
    if
    case x: bool :| true =>
      assert true || x;
  }
  0
}
