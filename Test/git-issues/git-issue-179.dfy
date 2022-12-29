// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
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
