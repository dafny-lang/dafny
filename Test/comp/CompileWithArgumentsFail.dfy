// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /compileTarget:cs "%s" --args csharp 1 >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main(args: int) {
  print "ok", args;
}
