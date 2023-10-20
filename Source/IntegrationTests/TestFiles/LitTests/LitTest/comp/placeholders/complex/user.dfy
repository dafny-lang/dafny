// RUN: %baredafny run %args %s --target=java --build=%S/Build/build --input %S/Inputs/wrappers.dfy --input %S/Inputs/random.dfy --input %S/Inputs/randomJava.dfy --input %S/Inputs/Interop/__default.java > "%t"
// RUN: %baredafny run %args %s --build=%S/Build/build --input %S/Inputs/wrappers.dfy --input %S/Inputs/random.dfy --input %S/Inputs/randomCSharp.dfy --input %S/Inputs/Interop.cs >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var x := DfyRandom.GetRandomNat(1000000);
  var y := 0;
  var i := 5;
  while(x != y && i != 0) {
    y := DfyRandom.GetRandomNat(1000000);
    i := i - 1;
  }
  var areEqual := x == y;
  print "areEqual: ", areEqual;
}