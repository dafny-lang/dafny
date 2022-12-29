// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Ref<A> {
  var val : A
  constructor (a : A)
    ensures val == a
  {
    val := a;
  }
}

method Main() {
  // simple
  print "1 = ", (x => x)(1), "\n";
  print "3 = ", (x => y => x + y)(1)(2), "\n";
  print "3 = ", ((x,y) => y + x)(1,2), "\n";
  print "0 = ", (() => 0)(), "\n";

  // local variable
  var y := 1;
  var f := x => x + y;
  print "3 = ", f(2), "\n";
  print "4 = ", f(3), "\n";
  y := 2;
  print "3 = ", f(2), "\n";
  print "4 = ", f(3), "\n";

  // reference
  var z := new Ref(1);
  f := x reads z => x + z.val;
  print "3 = ", f(2), "\n";
  print "4 = ", f(3), "\n";
  z.val := 2;
  print "4 = ", f(2), "\n";
  print "5 = ", f(3), "\n";

  // loop
  f := x => x;
  y := 10;
  while y > 0
    invariant forall x :: f.requires(x)
    invariant forall x :: f.reads(x) == {}
  {
    f := x => f(x+y);
    y := y - 1;
  }
  print "55 = ", f(0), "\n";

  // substitution test
  print "0 = ", (x => var y:=x;y)(0), "\n";
  print "1 = ", (y => (x => var y:=x;y))(0)(1), "\n";
}

