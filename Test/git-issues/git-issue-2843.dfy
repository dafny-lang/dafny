// RUN: %exits-with 2 %dafny /functionSyntax:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function F(ghost x: int, y: int): int {
  y
}

ghost function G(x: int, y: int): int {
  y
}

method M0() {
  var f: (int, int) -> int;
  f := F; // error: the expression `F` is ghost, since function F has a ghost parameter
  print F(2, 3), " ", f(2, 3), "\n";
}

method M1() {
  var g: (int, int) -> int;
  g := G; // error: G is ghost
  print g(2, 3), "\n";
}

method M2() {
  ghost var f: (int, int) -> int;
  f := F; // fine, since f is ghost
  f := G; // fine
}

method M3() {
  var f := F; // f is auto-ghost
  var g := G; // g is auto-ghost
  print f(2, 3), " ", g(2, 3), "\n"; // error (x2): f and g are ghost

  var tuple0: (ghost (int, int) -> int, int, ghost (int, int) -> int);
  tuple0 := (ghost F, 10, ghost G);
  tuple0 := (ghost f, 10, ghost g);
  print tuple0, "\n";

  var tuple1; // type is inferred (same as for tuple0 above)
  tuple1 := (ghost F, 10, ghost G);
  tuple1 := (ghost f, 10, ghost g);
  print tuple1, "\n";

  var tuple2: ((int, int) -> int, int, (int, int) -> int);
  tuple2 := (F, 10, G); // error (x2): F has ghost parameters and G is ghost
  tuple2 := (f, 10, g); // error (x2): f and g are ghost variables
  print tuple2, "\n";

  ghost var tuple3: ((int, int) -> int, int, (int, int) -> int);
  tuple3 := (F, 10, G);
  tuple3 := (f, 10, g);
  print tuple3, "\n"; // error: cannot print a ghost
}
