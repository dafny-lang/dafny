// RUN: %build --verbose --target cs "%s" > "%t"
// RUN: dotnet %S/CompileAndThenRun.dll >> "%t"

// RUN: %build --verbose --target js "%s" >> "%t"
// RUN: node %S/CompileAndThenRun.js >> "%t"

// RUN: %build --verbose --target go "%s" >> "%t"
// RUN: %S/CompileAndThenRun >> "%t"

// RUN: %build --verbose --target java "%s" >> "%t"
// RUN: java -cp %binaryDir/DafnyRuntime.jar%{pathsep}%S/CompileAndThenRun.jar CompileAndThenRun >> "%t"

// RUN: %build --unicode-char false --verbose --target cpp "%s" >> "%t"
// RUN: %S/CompileAndThenRun.exe >> "%t"

// RUN: %build --verbose --target py "%s" >> "%t"
// RUN: python3 %S/CompileAndThenRun-py >> "%t"

// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
