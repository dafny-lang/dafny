// RUN: %dafny /compileTarget:cs "%s" > "%t"
// RUN: dotnet %S/CompileRunQuietly.dll >> "%t"

// RUN: %dafny /compileTarget:js "%s" >> "%t"
// RUN: node %S/CompileRunQuietly.js >> "%t"

// RUN: %dafny /compileTarget:go "%s" >> "%t"
// RUN: %S/CompileRunQuietly >> "%t"

// RUN: %dafny /compileTarget:java "%s" >> "%t"
// RUN: java -cp %binaryDir/DafnyRuntime.jar:%S/CompileRunQuietly-java CompileRunQuietly >> "%t"

// RUN: %dafny /compileTarget:cpp "%s" >> "%t"
// RUN: %S/CompileRunQuietly.exe >> "%t"

// RUN: %dafny /compileTarget:py "%s" >> "%t"
// RUN: python3 %S/CompileRunQuietly-py/CompileRunQuietly.py >> "%t"

 // RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
