// RUN: %baredafny build %args --verbose --target=cs "%s" > "%t"
// RUN: dotnet %S/CompileAndThenRun.dll >> "%t"

// RUN: %baredafny build %args --verbose --target=js "%s" >> "%t"
// RUN: node %S/CompileAndThenRun.js >> "%t"

// RUN: %baredafny build %args --verbose --target=go "%s" >> "%t"
// RUN: %S/CompileAndThenRun >> "%t"

// RUN: %baredafny build %args --verbose --target=java "%s" >> "%t"
// RUN: java -cp %binaryDir/DafnyRuntime.jar:%S/CompileAndThenRun-java CompileAndThenRun >> "%t"

// RUN: %baredafny build %args --verbose --target=cpp "%s" >> "%t"
// RUN: %S/CompileAndThenRun.exe >> "%t"

// RUN: %baredafny build %args --verbose --target=py "%s" >> "%t"
// RUN: python3 %S/CompileAndThenRun-py/CompileAndThenRun.py >> "%t"

// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
