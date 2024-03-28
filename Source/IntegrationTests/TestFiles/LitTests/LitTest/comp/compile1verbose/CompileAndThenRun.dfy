// RUN: %dafny --unicode-char false /compileVerbose:1 --target cs "%s" > "%t"
// RUN: dotnet %S/CompileAndThenRun.dll >> "%t"

// RUN: %dafny --unicode-char false /compileVerbose:1 --target js "%s" >> "%t"
// RUN: node %S/CompileAndThenRun.js >> "%t"

// RUN: %dafny --unicode-char false /compileVerbose:1 --target go "%s" >> "%t"
// RUN: %S/CompileAndThenRun >> "%t"

// RUN: %dafny --unicode-char false /compileVerbose:1 --target java "%s" >> "%t"
// RUN: java -cp %binaryDir/DafnyRuntime.jar%{pathsep}%S/CompileAndThenRun-java CompileAndThenRun >> "%t"

// RUN: %dafny --unicode-char false /compileVerbose:1 --target cpp "%s" >> "%t"
// RUN: %S/CompileAndThenRun.exe >> "%t"

// RUN: %dafny --unicode-char false /compileVerbose:1 --target py "%s" >> "%t"
// RUN: python3 %S/CompileAndThenRun-py >> "%t"

// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
