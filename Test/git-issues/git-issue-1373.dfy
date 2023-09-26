// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var x := map[1 := () => 1];
  print x.Values; // error: map range type must support equality
  print x.Items; // error: map range type must support equality
}