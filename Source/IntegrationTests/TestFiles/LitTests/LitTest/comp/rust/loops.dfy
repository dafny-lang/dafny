// NONUNIFORM: Temporary development of the Rust compiler
// RUN: %baredafny run --target=rs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype u8 = x: int | 0 <= x < 10

method ToSet<T>(s: seq<T>) returns (r: set<T>) {
  if |s| == 0 {
    return {};
  }
  return {s[0]};
}

datatype Result<T> = Success(value: T)

method Main() {
  var x := map[1 := "hello", 2 := "world"];
  expect forall k <- x :: |x[k]| == 5;
  print x[1], " ", x[2], "\n";
  var z := map k <- x :: (k + 1) := x[k];
  print z[2], " ", z[3];
  var t := ToSet([1]);
  print t;

  var u8toInt := map[1 as u8 := 1, 2 as u8 := 2];
  var IntToU8 := map k <- u8toInt :: u8toInt[k] := k;
  var helloWorldAgain := map k <- u8toInt :: x[u8toInt[k]] := Success(k);

  var s := map[1 := Success("hello"), 2 := Success("world")];
  var is_result := forall k, k' | k in s && k' in s:: k != k' ==> s[k].value != s[k'].value;
  expect is_result;
}