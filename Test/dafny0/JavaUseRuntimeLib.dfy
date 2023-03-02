// RUN: %dafny "%s" /useRuntimeLib /out:%S/Output/DafnyConsole.jar /compileTarget:java > "%t"
// The next line fails to run because dafny/Helpers is not found on the class path.
// It's unclear why not.
// java -jar %S/Output/DafnyConsole.jar -cp %S/Output/DafnyConsole-java >> "%t"
// RUN: %diff "%s.expect" "%t"

module DafnyConsole {
  method Main() {
    print "bye\n";
  }
}
