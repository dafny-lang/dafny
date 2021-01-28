// RUN: %dafny /compileVerbose:1 /compileTarget:cs "%s" > "%t"
// RUN: dotnet CompileAndThenRun.dll >> "%t"
// RUN: %dafny /compileVerbose:1 /compileTarget:js "%s" >> "%t"
// RUN: node CompileAndThenRun.js >> "%t"
// RUN: %dafny /compileVerbose:1 /compileTarget:go "%s" >> "%t"
// RUN: go run CompileAndThenRun-go/src/CompileAndThenRun.go >> "%t"
// RUN: %dafny /compileVerbose:1 /compileTarget:java "%s" >> "%t"
// RUN: java CompileAndThenRun >> "%t"
// RUN: ./CompileAndThenRun >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
