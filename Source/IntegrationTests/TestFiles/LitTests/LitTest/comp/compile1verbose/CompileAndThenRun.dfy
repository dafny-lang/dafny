// RUN: %dafny /unicodeChar:0 /compileVerbose:1 /compileTarget:cs "%s" > "%t"
// RUN: dotnet %S/CompileAndThenRun.dll >> "%t"

// RUN: %dafny /unicodeChar:0 /compileVerbose:1 /compileTarget:js "%s" >> "%t"
// RUN: node %S/CompileAndThenRun.js >> "%t"

// RUN: %build --target:go --unicode-char:false --verbose "%s" >> "%t"
// RUN: %S/CompileAndThenRun >> "%t"

// RUN: %build --target:java --unicode-char:false --verbose "%s" >> "%t"
// RUN: java -cp %binaryDir/DafnyRuntime.jar%{pathsep}%S/CompileAndThenRun.jar CompileAndThenRun >> "%t"

// RUN: %dafny /unicodeChar:0 /compileVerbose:1 /compileTarget:cpp "%s" >> "%t"
// RUN: %S/CompileAndThenRun.exe >> "%t"

// RUN: %dafny /unicodeChar:0 /compileVerbose:1 /compileTarget:py "%s" >> "%t"
// RUN: python3 %S/CompileAndThenRun-py >> "%t"

// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
