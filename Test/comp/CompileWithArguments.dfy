// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" -- csharp 1 >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cpp "%s" -- cpp Yipee >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" -- java heya >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" -- javascript 2 >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" -- python 1 >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" -- "go go" 1 >> "%t"
// RUN: %dafny /noVerify /compile:2 /compileTarget:cs "%s" /out:%s.dll
// RUN: dotnet %s.dll "ellel" 2 >> "%t"
// RUN: dotnet %s.dll "on the go" 1 >> "%t"
// RUN: dotnet %s.dll "dll" "Aloha from" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main(args: seq<string>) {
  if |args| != 3 {
    print "Expected 3 arguments, got ", |args|;
  } else {
    var executable := args[0];
    if |executable| < 24 {
      print executable, " says ";
    } else {
      print "Someone says ";
    }
    if args[2] == "1" {
      print "Hello ",args[1], "\n";
    } else if args[2] == "2" {
      print "Howdy ", args[1], "\n";
    } else {
      print args[2], " ", args[1], "\n";
    }
  }
}