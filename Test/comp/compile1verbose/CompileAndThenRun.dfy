// RUN: %dafny /unicodeChar:0 /compileVerbose:1 /compileTarget:cs "%s" > "%t"
// RUN: dotnet %S/CompileAndThenRun.dll >> "%t"

// RUN: %dafny /unicodeChar:0 /compileVerbose:1 /compileTarget:js "%s" >> "%t"
// RUN: node %S/CompileAndThenRun.js >> "%t"

// RUN: %dafny /unicodeChar:0 /compileVerbose:1 /compileTarget:go "%s" >> "%t"
// RUN: %S/CompileAndThenRun >> "%t"

// RUN: %dafny /unicodeChar:0 /compileVerbose:1 /compileTarget:java "%s" >> "%t"
// RUN: java -cp %binaryDir/DafnyRuntime.jar:%S/CompileAndThenRun-java CompileAndThenRun >> "%t"

// RUN: %dafny /unicodeChar:0 /compileVerbose:1 /compileTarget:cpp "%s" >> "%t"
// RUN: %S/CompileAndThenRun.exe >> "%t"

// RUN: %dafny /unicodeChar:0 /compileVerbose:1 /compileTarget:py "%s" >> "%t"
// RUN: python3 %S/CompileAndThenRun-py/CompileAndThenRun.py >> "%t"

// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
