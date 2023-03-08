// RUN: %dafny /unicodeChar:0 /compileTarget:cs "%s" > "%t"
// RUN: dotnet %S/CompileRunQuietly.dll >> "%t"

// RUN: %dafny /unicodeChar:0 /compileTarget:js "%s" >> "%t"
// RUN: node %S/CompileRunQuietly.js >> "%t"

// RUN: %dafny /unicodeChar:0 /compileTarget:go "%s" >> "%t"
// RUN: %S/CompileRunQuietly >> "%t"

// RUN: %dafny /unicodeChar:0 /compileTarget:java "%s" >> "%t"
// RUN: java -cp %binaryDir/DafnyRuntime.jar:%S/CompileRunQuietly-java CompileRunQuietly >> "%t"

// RUN: %dafny /unicodeChar:0 /compileTarget:cpp "%s" >> "%t"
// RUN: %S/CompileRunQuietly.exe >> "%t"

// RUN: %dafny /unicodeChar:0 /compileTarget:py "%s" >> "%t"
// RUN: python3 %S/CompileRunQuietly-py/CompileRunQuietly.py >> "%t"

 // RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
