// NONUNIFORM: Temporary development of the Rust compiler
// RUN: %baredafny run --target=rs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype uint8 = x: int | 0 <= x < 256

type ValidUTF8Bytes = i: seq<uint8> | ValidUTF8Seq(i) witness []
predicate ValidUTF8Seq(i: seq<uint8>) { true }
type Utf8Bytes = ValidUTF8Bytes
type EncryptionContextKeys = seq<Utf8Bytes>

predicate Test(contextKeys: EncryptionContextKeys, result: EncryptionContextKeys) {
  forall k <- contextKeys :: k in result
}

method Main() {
  expect Test([[1 as uint8]], [[1 as uint8], [2 as uint8]]);
  expect !Test([[1 as uint8], [3 as uint8]], [[1 as uint8], [2 as uint8]]);
  var col := [-1, 1, 2];
  expect forall n: nat <- col :: n > 0;
  print "Everything is ok.";
}