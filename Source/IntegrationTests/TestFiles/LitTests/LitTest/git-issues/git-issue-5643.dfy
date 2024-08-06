// RUN: %testDafnyForEachCompiler "%s"

datatype D = A | B

const c := set d: D | true :: d

method Main() {
  print c, "\n";
}