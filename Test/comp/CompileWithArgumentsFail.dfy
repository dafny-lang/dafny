// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny_0 /noVerify /compile:4 /compileTarget:cs "%s" -- csharp 1 >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main(args: int) {
  print "ok", args;
}