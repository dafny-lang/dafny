// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

method Main() {
  var m: multiset<()> := multiset{};
  m := m[() := 18446744073709551616];
  print |m|, "\n";
}
