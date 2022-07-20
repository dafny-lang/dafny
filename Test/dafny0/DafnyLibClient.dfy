// RUN: %dafny /spillTargetCode:1 %S/DafnyLib.dfy %S/DafnyLib-extern.cs /useRuntimeLib /out:%S/Output/DafnyLib.dll /compileTarget:cs > "%t"
// RUN: %dafny /spillTargetCode:1 /compile:3 "%s" %S/Output/DafnyLib.dll >> "%t"
// RUN: %diff "%s.expect" "%t"

module Client {
  import Library  // this lives in DafnyLib.dll
  import AmbiguousNestedModule = Library.AmbiguousNestedModule
  method Main() {
    Library.EntryPoint();
    AmbiguousNestedModule.EntryPoint();
    print "bye\n";
  }
}
