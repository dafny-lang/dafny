// RUN: %baredafny run --target=js "%s" --input "%S/git-issue-2956b.js" > "%t"
// RUN: %diff "%s.expect" "%t"

method {:extern "global", "OneOne"} OneOne() returns (s: seq<int>)

method Main() {
  var s := OneOne();
  expect s == [1];
}
