// RUN: %baredafny run %args %s --build=%S/Build/build --input %S/wrappers.dfy --input %S/random.dfy --input %S/randomCSharp.dfy --input %S/Interop.cs --spill-target-code > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var x := DfyRandom.GetRandomNat(10);
  var y := DfyRandom.GetRandomNat(10);
  var areEqual := x == y;
  print "areEqual: ", areEqual;
}