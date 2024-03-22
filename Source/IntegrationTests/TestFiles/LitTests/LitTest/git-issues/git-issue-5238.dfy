// RUN: %testDafnyForEachCompiler "%s"

method Main() {
  var s: seq<char>;
  s := *;
  print "(", s, ")\n";
}
