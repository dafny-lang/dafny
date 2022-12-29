// RUN: %baredafny verify %args "%s" > "%t"
// RUN: ! %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: ! %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: ! %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: ! %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
   expect false;
}
