// RUN: %verify "%s" > "%t"
// RUN: %exits-with 3 %run --no-verify --target cs "%s" csharp 1 >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main(args: array<string>, dummy: int) {
  print "ok", dummy;
}
