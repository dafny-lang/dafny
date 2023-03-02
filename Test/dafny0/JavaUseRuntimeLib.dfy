// RUN: %dafny "%s" /useRuntimeLib /out:%S/Output/DafnyConsole.jar /compileTarget:java > "%t"
// RUN: java -jar %S/Output/DafnyConsole.jar -cp %S/Output/DafnyConsole-java >> "%t"
// RUN: %diff "%s.expect" "%t"

module DafnyConsole {
  method Main() {
    print "bye\n";
  }
}
