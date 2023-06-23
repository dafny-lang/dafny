// RUN: %testDafnyForEachCompiler "%s"

method Main() {
  expect IsEmpty("");
}

predicate IsEmpty<T>(s: seq<T>) {
  s == []
}
