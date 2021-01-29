// RUN: %dafny /compileTarget:cs "%s" > "%t"
// RUN: dotnet CompileRunQuietly.dll >> "%t"

// RUN: %dafny /compileTarget:js "%s" >> "%t"
// RUN: node CompileRunQuietly.js >> "%t"

// RUN: %dafny /compileTarget:go "%s" >> "%t"
// RUN: ./CompileRunQuietly >> "%t"

// RUN: %dafny /compileTarget:java "%s" >> "%t"
// RUN: java CompileRunQuietly >> "%t"

// RUN: %dafny /compileTarget:cpp "%s" >> "%t"
// RUN: ./CompileRunQuietly.exe >> "%t"

// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
