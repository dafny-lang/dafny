// RUN: %dafny "%s" /useRuntimeLib /out:%S/Output/DafnyConsole.jar /compileTarget java > "%t"
// RUN: java -cp %binaryDir/DafnyRuntime.jar%{pathsep}%S/Output/DafnyConsole.jar DafnyConsole >> "%t"
// RUN: %diff "%s.expect" "%t"

module DafnyConsoleMod { // TODO if we name this DafnyConsole, then Java compilation fails
  method Main() {
    print "bye\n";
  }
}
