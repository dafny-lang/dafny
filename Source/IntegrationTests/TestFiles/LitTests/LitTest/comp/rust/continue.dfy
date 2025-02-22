// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %baredafny run --target=rs --raw-pointers --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var valuesArray := new int[8](i => i);
  var values1a := valuesArray[1..];
  expect values1a == [1, 2, 3, 4, 5, 6, 7];
  var values1b := valuesArray[..7];
  expect values1b == [0, 1, 2, 3, 4, 5, 6];
  var values1c := valuesArray[..];
  expect values1c == [0, 1, 2, 3, 4, 5, 6, 7];
  var values1 := valuesArray[1..8];
  expect values1 == values1a;
  var values2 := values1[1..];
  expect values2 == [2, 3, 4, 5, 6, 7];
  var values3 := values1[..5];
  expect values3 == [1, 2, 3, 4, 5];
  var values4 := values1[..];
  expect values4 == [1, 2, 3, 4, 5, 6, 7];
  var values := values1[0..6];
  expect values == [1, 2, 3, 4, 5, 6];
  var acc := 0;
  for i := 0 to |values|
  {
    if values[i] % 3 == 0 {
      acc := acc + 3;
      continue;
    }
    if (5 <= values[i]) == true {
       break;
    }
    acc := acc + values[i];
  }
  print acc, "\n";
}