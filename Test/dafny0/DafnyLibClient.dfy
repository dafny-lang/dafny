// This test isn't possible with the new CLI commands, because it wants to compile a Dafny library to a .dll
// and use that as part of another Dafny project. It expects the Dafny source of the library to be included in the .dll
// as a Source attribute. However, 'dafny build' and `dafny run` always include the Dafny runtime,
// so the new UI will include the runtime twice for this test causing it to fail. 

// In the new UI, consuming a Dafny library in Dafny is done by consuming the library's Dafny source, 
// instead of a .dll that includes the Dafny source.

// RUN: %dafny /spillTargetCode:1 %S/DafnyLib.dfy %S/DafnyLib-extern.cs /useRuntimeLib /out:%S/Output/DafnyLib.dll /compileTarget:cs > "%t"
// RUN: %dafny /spillTargetCode:1 /compile:3 "%s" %binaryDir/DafnyRuntime.dll %S/Output/DafnyLib.dll >> "%t"
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
