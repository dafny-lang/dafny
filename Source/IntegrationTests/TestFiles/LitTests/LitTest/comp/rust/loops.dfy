// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype u8 = x: int | 0 <= x < 10

method ToSet<T>(s: seq<T>) returns (r: set<T>) {
  if |s| == 0 {
    return {};
  }
  return {s[0]};
}

newtype U8 = x: int | 0 <= x <= 255
type ByteSequence = seq<U8>

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

  var zeroContainer := new ZeroContainer();
  zeroContainer.i := 0;
  expect exists i: int | zeroContainer.i <= i < 10 :: i % 3 == 2;
  expect forall i: int | 1 <= i <= 10 :: i % 11 != 0;
  var c := "abcdaa";
  expect forall ch <- c :: ch !in "e";

  Remap();

  // ExactBoundedPool
  expect forall i: int | i == 1 :: i % 2 == 1;
  expect (map i: int | i == 1 :: i % 2 := 2) == map[1 := 2];

  // MultisetBoundedPool
  expect forall i: int | i in multiset{1, 1, 3} :: i % 2 == 1;
  expect (map i: int | i in multiset{1, 1, 3} :: i % 2 := 2) == map[1 := 2];
}

method Remap() {
  var sResults: map<ByteSequence, Result<(string, string)>> := map[
    [2 as U8] := Success(("abc", "def")),
    [3 as U8, 4 as U8] := Success(("abc2", "def2"))
  ];
  var remapped := map r | r in sResults.Values :: r.value.0 := r.value.1;
  expect "abc" in remapped && remapped["abc"] == "def";
  expect "abc2" in remapped && remapped["abc2"] == "def2";
}

class ZeroContainer {
  var i: int
  constructor() {
    i := 0;
  }
}