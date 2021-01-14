// RUN: %dafny /compileTarget:cs "%s" > "%t"
// RUN: dotnet run CompileAndThenRun.dll >> "%t"
// RUN: %dafny /compileTarget:js "%s" >> "%t"
// RUN: node CompileAndThenRun.js >> "%t"
// RUN: %dafny /compileTarget:go "%s" >> "%t"
// RUN: go run CompileAndThenRun-go/src/CompileAndThenRun.go >> "%t"
// RUN: %dafny /compileTarget:java "%s" >> "%t"
// RUN: java CompileAndThenRun-java/dafny/CompileAndThenRun >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
