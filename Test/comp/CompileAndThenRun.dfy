// RUN: %dafny /compileVerbose:1 /compileTarget:cs "%s" > "%t"
// RUN: dotnet CompileAndThenRun.dll >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
