// RUN: echo ""

method Foo() {
  var y := 3;
  if (true) {
    var y := 4;
  }
}