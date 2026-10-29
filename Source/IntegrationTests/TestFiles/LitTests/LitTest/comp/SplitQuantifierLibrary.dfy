// RUN: %dafny /compileTarget:cs /useRuntimeLib /out:%S/Output/SplitQuantifierLib.dll %S/Inputs/SplitQuantifierLib.dfy > "%t"
// RUN: %dafny /compile:3 "%s" %binaryDir/DafnyRuntime.dll %S/Output/SplitQuantifierLib.dll >> "%t"
// RUN: %diff "%s.expect" "%t"

// The library's assembly embeds the library's Dafny source, which Dafny resolves again here. It has the quantifier as
// written, whose antecedent bounds i, as the resolver requires of a compiled quantifier.
module Client {
  import Library

  method Main() {
    print Library.Small(10), " ", Library.Small(11), "\n";
  }
}
