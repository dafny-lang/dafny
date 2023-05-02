// RUN: echo ""

method Bar() {
  var x := 3;
  if (true) {
    var x := 4;
  }
}