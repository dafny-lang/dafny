// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny_0 /noVerify /compile:4 /compileTarget:cs /arg:csharp /arg:1 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main(args: array<string>, dummy: int) {
  print "ok", dummy;
}