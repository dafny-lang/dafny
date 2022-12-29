// RUN: %baredafny run %args --target=cs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "Hello world\n";
}
