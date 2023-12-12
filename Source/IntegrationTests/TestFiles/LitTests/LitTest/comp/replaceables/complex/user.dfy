// RUN: %build --target=lib --output=%S/Build/build %S/Inputs/wrappers.dfy %S/Inputs/random.dfy > "%t"
// RU2N: %build --target=java --output=%S/Build/build %S/Build/build.doo %S/Inputs/randomJava.dfy  %S/Inputs/Interop/__default.java > "%t"
// RU2N: %run %s --target=java --build=%S/Build/build --library=%S/Build/build.doo --input %S/Build/build.jar > "%t"
// RUN: %build --target=cs --output=%S/Build/build %S/Build/build.doo %S/Inputs/randomCSharp.dfy  %S/Inputs/Interop.cs >> "%t"
// RUN: %run %s --target=cs --build=%S/Build/build --library=%S/Build/build.doo --input %S/Build/build.dll >> "%t"
// RU2N: %baredafny run %args %s --build=%S/Build/build --input %S/Inputs/wrappers.dfy --input %S/Inputs/random.dfy --input %S/Inputs/randomCSharp.dfy --input %S/Inputs/Interop.cs >> "%t"
// RUN: %diff "%s.expect" "%t"

// Test can fail non-deterministically by design, but the chance is ~10^-30
method Main() {
  var x := DfyRandom.GetRandomNat(1000000);
  var y := 0;
  var i := 5;
  while(x != y && i != 0)
    decreases i
  {
    y := DfyRandom.GetRandomNat(1000000);
    i := i - 1;
  }
  expect i == 0 || x != y;
}