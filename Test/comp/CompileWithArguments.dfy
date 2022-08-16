// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs /arg:csharp /arg:1 "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java /arg:java /arg:heya "%s" >> "%t"
// RN: %dafny /noVerify /compile:4 /compileTarget:js /arg:javascript /arg:2 "%s" >> "%t"
// RN: %dafny /noVerify /compile:4 /compileTarget:go "/arg:go go" /arg:1 "%s" >> "%t"
// RN: %dafny /noVerify /compile:4 /compileTarget:py "/arg:python /arg:1 "%s" >> "%t"
// RUN: %dafny /noVerify /compile:2 /compileTarget:cs "%s" /out:%s.dll
// RUN: dotnet %s.dll "ellel" 2 >> "%t"
// RUN: dotnet %s.dll "on the go" 1 >> "%t"
// RUN: dotnet %s.dll "dll" "Aloha from" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main(args: array<string>) {
  if args.Length != 2 {
    print "Expected 2 arguments, got ", args.Length;
  } else {
    if args[1] == "1" {
      print "Hello ",args[0], "\n";
    } else if args[1] == "2" {
      print "Howdy ", args[0], "\n";
    } else {
      print args[1], " ", args[0], "\n";
    }
  }
}