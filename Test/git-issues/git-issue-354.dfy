// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

class C<X(0)> {
  static const u: X
}

method Main() {
  print C<int>.u, "\n";
  print C<nat>.u, "\n";
  print C<real>.u, "\n";
  print C<bool>.u, "\n";
}

