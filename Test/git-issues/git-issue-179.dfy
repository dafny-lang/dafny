// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var mp: map<int,bool>;
  mp := mp[5 := false][4 := true][3 := false];
  var i := mp.Items;
  print i, "\n";
  print mp.Keys, "\n";
  print mp.Values, "\n";

  print 5 in mp, " ", 9 in mp, " ", 8 !in mp, " ",  4 !in mp, "\n";
}
