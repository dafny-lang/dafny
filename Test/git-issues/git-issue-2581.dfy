// RUN: %testDafnyForEachCompiler "%s"

method Main() {
  expect IsEmpty("");
}

predicate method IsEmpty<T>(s: seq<T>) {
  s == []
}
