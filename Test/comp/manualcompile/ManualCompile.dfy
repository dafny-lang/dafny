// RUN: %dafny /compileVerbose:1 /compile:0 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: dotnet build ManualCompile.csproj
// RUN: dotnet bin/Debug/net5.0/ManualCompile.dll >> "%t"

// RUN: %dafny /compileVerbose:1 /compile:0 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: node ManualCompile.js >> "%t"

// RUN: %dafny /compileVerbose:1 /compile:0 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: go run ManualCompile-go/src/ManualCompile.go >> "%t"

// RUN: %dafny /compileVerbose:1 /compile:0 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: javac ManualCompile-java/ManualCompile.java ManualCompile-java/*/*.java
// RUN: java ManualCompile

// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
