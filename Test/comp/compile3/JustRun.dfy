// RUN: %baredafny run %args --verbose --target=cs "%s" > "%t"
// RUN: %baredafny run %args --verbose --target=js "%s" >> "%t"
// RUN: %baredafny run %args --verbose --target=go "%s" >> "%t"
// RUN: %baredafny run %args --verbose --target=java "%s" >> "%t"
// RUN: %baredafny run %args --verbose --target=cpp "%s" >> "%t"
// RUN: %baredafny run %args --verbose --target=py "%s" >> "%t"
// RUN: %baredafny run %args --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --target=js "%s" >> "%t"
// RUN: %baredafny run %args --target=go "%s" >> "%t"
// RUN: %baredafny run %args --target=java "%s" >> "%t"
// RUN: %baredafny run %args --target=cpp "%s" >> "%t"
// RUN: %baredafny run %args --target=py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
