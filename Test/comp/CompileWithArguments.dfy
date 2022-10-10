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