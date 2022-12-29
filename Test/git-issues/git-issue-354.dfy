// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

class C<X(0)> {
  static const u: X
}

method Main() {
  print C<int>.u, "\n";
  print C<nat>.u, "\n";
  print C<real>.u, "\n";
  print C<bool>.u, "\n";
}

