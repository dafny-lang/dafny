// RUN: %dafny /compileTarget:cs "%s" > "%t"
// RUN: dotnet CompileRunQuietly.dll >> "%t"

// RUN: %dafny /compileTarget:js /out:%S/CompileRunQuietly.js "%s" >> "%t"
// RUN: node %S/CompileRunQuietly.js >> "%t"

// RUN: %dafny /compileTarget:go /out:%S/CompileRunQuietly "%s" >> "%t"
// RUN: %S/CompileRunQuietly >> "%t"

// RUN: %dafny /compileTarget:java /out:%S/CompileRunQuietly "%s" >> "%t"
// RUN: java -cp %binaryDir/DafnyRuntime.jar:%S/CompileRunQuietly-java CompileRunQuietly >> "%t"

// RUN: %dafny /compileTarget:cpp "%s" >> "%t"
// RUN: %S/CompileRunQuietly.exe >> "%t"

// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
