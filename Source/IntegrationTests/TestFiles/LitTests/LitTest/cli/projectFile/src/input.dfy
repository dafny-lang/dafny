// RUN: echo ""

method Foo() {
  var x := 3;
  if (true) {
    var x := 4;
  }
}

ghost function Bar(): int {
  3
} 

method Main() {
  print "hello";
}