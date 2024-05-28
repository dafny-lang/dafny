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

datatype Result<T> = Success(value: T) | Failure(msg: string)

const CONST1: string := "1"
const CONST3: string := "3"
const CONST5: string := "5"
const PREFIX: string := "p_"

function PrependPrefix(p: string): string {
  PREFIX + p
}

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

  assert {:split_here} true;
  var successbool := Success(Success(true));
  expect successbool.value.value == true;
  var s := map[1 := Success("hello"), 2 := Success("world")];
  var is_result := forall k, k' | k in s && k' in s:: k != k' ==> s[k].value != s[k'].value;
  expect is_result;

  var zBefore := map["3" := "5", "5" := "7"];
  assert {:split_here} true;

  forall k <- zBefore, k' <- zBefore ensures k != k' ==> PrependPrefix(k) != PrependPrefix(k') {
    if PrependPrefix(k) == PrependPrefix(k') {
      assert k == PrependPrefix(k)[2..];
      assert k' == PrependPrefix(k')[2..];
      assert k == k';
    }
  }
  var zAfter := map[
      CONST1 := "b",
      CONST3 := CONST1 + "c",
      CONST5 := "1"
    ] + map k <- zBefore :: PrependPrefix(k) := zBefore[k];
  expect "p_3" in zAfter && zAfter["p_3"] == "5";
}