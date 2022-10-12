// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" --args Csharp 1 >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cpp "%s" --args Cpp yipee >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" --args Java heya >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" --args Javascript 2 >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" --args Python 1 >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" --args "Go go" 1 >> "%t"
// RUN: %dafny /noVerify /compile:2 /compileTarget:cs "%s" /out:%s.dll
// RUN: dotnet %s.dll "dotnet" 2 >> "%t"
// RUN: dotnet %s.dll "dotnet" 1 >> "%t"
// RUN: dotnet %s.dll "dotnet" "aloha" >> "%t"
// RUN: %dafny /noVerify /compile:2 /compileTarget:js "%s" /out:%s.js
// RUN: node %s.js "javascript" 2 >> "%t"
// RUN: node %s.js "javascript" 1 >> "%t"
// RUN: node %s.js "javascript" "aloha" >> "%t"
// RUN: %dafny /noVerify /compile:2 /compileTarget:cpp "%s" /out:%s.exe
// RUN: %s.exe "cpp" 2 >> "%t"
// RUN: %s.exe "cpp" 1 >> "%t"
// RUN: %s.exe "cpp" "aloha" >> "%t"
// RUN: %dafny /noVerify /compile:0 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: javac -cp %binaryDir/DafnyRuntime.jar:%S/CompileWithArguments-java %S/CompileWithArguments-java/CompileWithArguments.java %S/CompileWithArguments-java/*/*.java
// RUN: java -cp %binaryDir/DafnyRuntime.jar:%S/CompileWithArguments-java CompileWithArguments Java 2 >> "%t"
// RUN: java -cp %binaryDir/DafnyRuntime.jar:%S/CompileWithArguments-java CompileWithArguments Java 1 >> "%t"
// RUN: java -cp %binaryDir/DafnyRuntime.jar:%S/CompileWithArguments-java CompileWithArguments Java aloha >> "%t"
// RUN: %dafny /noVerify /compile:0 /spillTargetCode:2 /compileTarget:py "%s" >> "%t"
// RUN: python3 %S/CompileWithArguments-py/CompileWithArguments.py Python 2 >> "%t"
// RUN: python3 %S/CompileWithArguments-py/CompileWithArguments.py Python 1 >> "%t"
// RUN: python3 %S/CompileWithArguments-py/CompileWithArguments.py Python aloha >> "%t"
// RUN: %dafny /noVerify /compile:0 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: env GO111MODULE=auto GOPATH=%S/CompileWithArguments-go go run %S/CompileWithArguments-go/src/CompileWithArguments.go Go 2 >> "%t"
// RUN: env GO111MODULE=auto GOPATH=%S/CompileWithArguments-go go run %S/CompileWithArguments-go/src/CompileWithArguments.go Go 1 >> "%t"
// RUN: env GO111MODULE=auto GOPATH=%S/CompileWithArguments-go go run %S/CompileWithArguments-go/src/CompileWithArguments.go Go aloha >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main(args: seq<string>) {
  if |args| != 3 {
    print "Expected 3 arguments, got ", |args|;
  } else {
    print args[1], " says ";
    if args[2] == "1" {
      print "hello\n";
    } else if args[2] == "2" {
      print "howdy\n";
    } else {
      print args[2],"\n";
    }
  }
}