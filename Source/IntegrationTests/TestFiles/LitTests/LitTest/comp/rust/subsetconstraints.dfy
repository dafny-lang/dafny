// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %OutputCheck --file-to-check "%S/subsetconstraints-rust/src/subsetconstraints.rs" "%S/subsetconstraints.check"

newtype uint8 = x: int | 0 <= x < 256

type ValidSeqUint8 = i: seq<uint8> | SubtypePredicate(i) witness []
predicate SubtypePredicate(i: seq<uint8>) { true }
type SeqUint8 = ValidSeqUint8
type SeqSeqUInt8 = seq<SeqUint8>
type MoreThanOne = x: uint8 | x > 1 witness 2
type DummyType<T> = x: T | true witness *

predicate Test(contextKeys: SeqSeqUInt8, result: SeqSeqUInt8) {
  forall k <- contextKeys :: k in result
}

method AcceptSubsetAndType(x: MoreThanOne, y: uint8) {
  AcceptType(x);
}
method AcceptType(y: uint8) {
}

method AcceptSubsetAndType2(x: DummyType<MoreThanOne>, y: uint8) {
  AcceptType(x);
}
class TestOwnershipConstructor {
  constructor(a: SeqSeqUInt8, b: seq<seq<uint8>>, c: MoreThanOne, d: MoreThanOne) {
  }
}
method Main() {
  var s := [[1 as uint8]];
  var sSub: SeqSeqUInt8 := s;
  expect Test(s, [[1 as uint8], [2 as uint8]]);
  expect !Test([[1 as uint8], [3 as uint8]], [[1 as uint8], [2 as uint8]]);
  var col := [-1, 1, 2];
  expect forall n: nat <- col :: n > 0;
  var x := 2 as uint8;
  var y: MoreThanOne := 2;
  var y1: DummyType<MoreThanOne> := y;
  AcceptSubsetAndType(x, y); // Note that subset types are reversed
  AcceptSubsetAndType2(x, y); // Note that subset types are reversed
  AcceptSubsetAndType(x, y1); // Note that subset types are reversed
  AcceptSubsetAndType2(x, y1); // Note that subset types are reversed
  var z := new TestOwnershipConstructor(s, sSub, x, y);
  print "Everything is ok.";
}