// NONUNIFORM: https://github.com/dafny-lang/dafny/issues/4108
// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

method Main() {
  var mp: map<int,bool>;
  mp := mp[5 := false][4 := true][3 := false];
  var i := mp.Items;
  print i, "\n";
  print mp.Keys, "\n";
  print mp.Values, "\n";

  print 5 in mp, " ", 9 in mp, " ", 8 !in mp, " ",  4 !in mp, "\n";
}
