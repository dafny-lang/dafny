// RUN: %baredafny build %args --target=cs "%s" > "%t"
// RUN: dotnet %S/CompileRunQuietly.dll >> "%t"

// RUN: %baredafny build %args --target=js "%s" >> "%t"
// RUN: node %S/CompileRunQuietly.js >> "%t"

// RUN: %baredafny build %args --target=go "%s" >> "%t"
// RUN: %S/CompileRunQuietly >> "%t"

// RUN: %baredafny build %args --target=java "%s" >> "%t"
// RUN: java -cp %binaryDir/DafnyRuntime.jar:%S/CompileRunQuietly-java CompileRunQuietly >> "%t"

// RUN: %baredafny build %args --target=cpp "%s" >> "%t"
// RUN: %S/CompileRunQuietly.exe >> "%t"

// RUN: %baredafny build %args --target=py "%s" >> "%t"
// RUN: python3 %S/CompileRunQuietly-py/CompileRunQuietly.py >> "%t"

 // RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
