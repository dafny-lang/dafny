// RUN: %baredafny translate cs %args "%s" > "%t"
// RUN: dotnet build %S/ManualCompile.csproj
// RUN: dotnet %S/bin/Debug/net6.0/ManualCompile.dll >> "%t"

// RUN: %baredafny translate js %args "%s" >> "%t"
// RUN: node %S/ManualCompile.js >> "%t"

// RUN: %baredafny translate go %args  "%s" >> "%t"
// RUN: env GO111MODULE=auto GOPATH=%S/ManualCompile-go go run %S/ManualCompile-go/src/ManualCompile.go >> "%t"

// RUN: %baredafny translate java %args "%s" >> "%t"
// RUN: javac -cp %binaryDir/DafnyRuntime.jar:%S/ManualCompile-java %S/ManualCompile-java/ManualCompile.java %S/ManualCompile-java/*/*.java
// RUN: java -cp %binaryDir/DafnyRuntime.jar:%S/ManualCompile-java ManualCompile >> "%t"

// RUN: %baredafny translate cpp %args "%s" >> "%t"
// RUN: g++ -g -Wall -Wextra -Wpedantic -Wno-unused-variable -std=c++17 -I %binaryDir -o %S/ManualCompile.exe %S/ManualCompile.cpp
// RUN: %S/ManualCompile.exe >> "%t"

// RUN: %baredafny translate py %args  "%s" >> "%t"
// RUN: python3 %S/ManualCompile-py/ManualCompile.py >> "%t"

// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
