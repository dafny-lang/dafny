// RUN: %build --target cs "%s" > "%t"
// RUN: dotnet %S/CompileRunQuietly.dll >> "%t"

// RUN: %build --target js "%s" >> "%t"
// RUN: node %S/CompileRunQuietly.js >> "%t"

// RUN: %build --target go "%s" >> "%t"
// RUN: %S/CompileRunQuietly >> "%t"

// RUN: %build --target java "%s" >> "%t"
// RUN: java -cp %binaryDir/DafnyRuntime.jar%{pathsep}%S/CompileRunQuietly.jar CompileRunQuietly >> "%t"

// RUN: %build --unicode-char false --target cpp "%s" >> "%t"
// RUN: %S/CompileRunQuietly.exe >> "%t"

// RUN: %build --target py "%s" >> "%t"
// RUN: python3 %S/CompileRunQuietly-py >> "%t"

 // RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
