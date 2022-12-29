// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %exits-with 3 %baredafny run %args --no-verify --target=cs "%s" --args csharp 1 >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main(args: array<string>, dummy: int) {
  print "ok", dummy;
}
