// RUN: %dafny /compileVerbose:1 /compile:0 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: dotnet build ManualCompile.csproj
// RUN: dotnet bin/Debug/net5.0/ManualCompile.dll >> "%t"

// RUN: %dafny /compileVerbose:1 /compile:0 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: node ManualCompile.js >> "%t"

// RUN: %dafny /compileVerbose:1 /compile:0 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: go run ManualCompile-go/src/ManualCompile.go >> "%t"

// RUN: %dafny /compileVerbose:1 /compile:0 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: javac ManualCompile-java/ManualCompile.java ManualCompile-java/*/*.java
// RUN: java ManualCompile >> "%t"

// RUN: %diff "%s.expect" "%t"

/* In the future (when we've figured out how to obtain the right version of g++ on github),
 * C++ can be added by including these commands above:
 *
 *     %dafny /compileVerbose:1 /compile:0 /spillTargetCode:2 /compileTarget:cpp "%s" >> "%t"
 *     g++ -g -Wall -Wextra -Wpedantic -Wno-unused-variable -std=c++17 -I %binaryDir -o ManualCompile.exe ManualCompile.cpp
 *     ./ManualCompile.exe >> "%t"
 *
 * and adding "g++" to lit.local.cfg in this folder.
 */

method Main() {
  print "hello, Dafny\n";
}
