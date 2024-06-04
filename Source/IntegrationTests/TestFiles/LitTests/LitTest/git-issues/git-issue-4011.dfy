// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

method Main() {
  var a: multiset<bool> := multiset{false, true};
  var b: multiset<multiset<bool>> := multiset{a[true := 0]};

  print b == multiset{multiset{false}}, "\n";
  print b <= multiset{multiset{false}}, "\n";
  print multiset{multiset{false}} <= b, "\n";
  print b, "\n";
}
