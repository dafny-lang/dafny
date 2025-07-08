// RUN: %resolve %S/Input/high.dfyconfig.toml > %t
// RUN: %diff "%s.expect" "%t"

method Foo(x: int) {
  if (x == 0) {
    var x := 3;
    print x, "\n";
  }
}