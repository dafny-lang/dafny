// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0

method Main() {
  var m: multiset<()> := multiset{};
  m := m[() := 18446744073709551616];
  print |m|, "\n";
}
