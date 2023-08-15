// RUN: %testDafnyForEachCompiler "%s"

method Main() {
  var m: multiset<()> := multiset{};
  m := m[() := 18446744073709551616];
  print |m|, "\n";
}
