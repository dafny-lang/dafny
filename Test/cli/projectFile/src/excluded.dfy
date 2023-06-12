// RUN: echo ""

method Foo() {
  var z := 3;
  if (true) {
    var z := 4;
  }
}