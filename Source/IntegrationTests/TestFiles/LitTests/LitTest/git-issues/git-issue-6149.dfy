// RUN: %testDafnyForEachCompiler "%s"

predicate TestX(f: char -> bool) {
  f('x')
}

predicate TestXOn(obtained: char) {
  TestX((c: char) => c == obtained)
}

method Main() {
  var c := TestXOn('x');
  print c;
}