// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs /arg:csharp /arg:1 "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cpp /arg:cpp /arg:Yipee "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java /arg:java /arg:heya "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js /arg:javascript /arg:2 "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py /arg:python /arg:1 "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "/arg:go go" /arg:1 "%s" >> "%t"
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