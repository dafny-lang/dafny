// RUN: %dafny /compileVerbose:1 /compile:0 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: dotnet build %S/ManualCompile.csproj
// RUN: dotnet %S/bin/Debug/net6.0/ManualCompile.dll >> "%t"

// RUN: %dafny /compileVerbose:1 /compile:0 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: node %S/ManualCompile.js >> "%t"

// RUN: %dafny /compileVerbose:1 /compile:0 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: env GO111MODULE=auto GOPATH=%S/ManualCompile-go go run %S/ManualCompile-go/src/ManualCompile.go >> "%t"

// RUN: %dafny /compileVerbose:1 /compile:0 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: javac %S/ManualCompile-java/ManualCompile.java %S/ManualCompile-java/*/*.java
// RUN: java -cp %S/ManualCompile-java ManualCompile >> "%t"

// RUN: %dafny /compileVerbose:1 /compile:0 /spillTargetCode:2 /compileTarget:cpp "%s" >> "%t"
// RUN: g++ -g -Wall -Wextra -Wpedantic -Wno-unused-variable -std=c++17 -I %binaryDir -o %S/ManualCompile.exe %S/ManualCompile.cpp
// RUN: %S/ManualCompile.exe >> "%t"

// RUN: %dafny /compileVerbose:1 /compile:0 /spillTargetCode:2 /compileTarget:py "%s" >> "%t"
// RUN: python3 %S/ManualCompile-py/ManualCompile.py >> "%t"

// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
