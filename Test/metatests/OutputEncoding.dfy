// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run --no-verify --target=cs %args "%s" >> "%t"
// RUN: %baredafny run --no-verify --target=js %args  "%s" >> "%t"
// RUN: %baredafny run --no-verify --target=go %args  "%s" >> "%t"
// RUN: %baredafny run --no-verify --target=java %args  "%s" >> "%t"
// RUN: %baredafny run --no-verify --target=py %args  "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "Euro sign: " + [0x20AC as char], "\n"; // €
}
