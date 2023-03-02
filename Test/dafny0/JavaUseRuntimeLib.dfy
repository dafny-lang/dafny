// RUN: %dafny "%s" /useRuntimeLib /out:%S/Output/DafnyConsole.jar /compileTarget:java > "%t"
// RUN: java -cp %binaryDir/DafnyRuntime.jar:%S/Output/DafnyConsole.jar DafnyConsole >> "%t"
// RUN: %diff "%s.expect" "%t"

module DafnyConsole {
  method Main() {
    print "bye\n";
  }
}
