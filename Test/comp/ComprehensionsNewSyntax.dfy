// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  Quantifier();
  MapComprehension();
  OutParamsUnderLambdas();  // white-box testing
  SetComprehension();
  Enumerations();
  EnumerationsMaybeNull();
  TestImplicitTypeTests.Test();
}

function method FourMore(x: int): int { x + 4 }

method Quantifier() {
  // Note, by making *two* assignments to "s" (instead of the obvious one), the direct translation
  // into Java makes "s" NOT be "effectively final". This means that Java does not allow "s" to be
  // used in the lambda expression into which the quantifier translates. Compilation into Java
  // thus needs to capture the value of "s" into another variable, which these tests check on.
  var s := [0, 1, 1, 2];
  s := s + [3, 5, 8, 13];
  print forall x <- s :: x < 20, " ";  // true
  print forall x <- s :: x < 10, "\n";  // false
  print exists x <- s :: x == 3, " ";  // true
  print exists x <- s :: x == 4, "\n";  // false
}

method MapComprehension() {
  var s := [12, 13, 14];
  var m := map x <- s :: x / 2;
  print m, "\n";
  m := map x <- s :: FourMore(x) := x;
  print m, "\n";
}

method OutParamsUnderLambdas() {
  var x, b := XP();
  print "XP returned: ", x, " ", b, "\n";
  var m := XM();
  print "XM returned: ", m, "\n";
}

method XP() returns (x: int, b: bool) {
  var s := {2, 4};
  b := exists y <- s :: y < x;
}


method XM() returns (x: int) {
  var before, after;

  var f := () => x;
  before := f();
  x := 2;
  after := f();
  print "after: ", f(), " ", "before: ", f(), "\n";

  f := () => x;
  before := f();
  x := 16;
  after := f();
  print "after: ", f(), " ", "before: ", f(), "\n";
}

trait NothingInParticular { }
class ClassA { }
class ClassB extends NothingInParticular { }

method SetComprehension() {
  SetComprehension0();
  SetComprehension1();
  SetComprehension2();
  SetComprehension3();
}

method SetComprehension0() {
  var w, x, y, z := new ClassA, new ClassA, new ClassB, new ClassB;
  var s := {w, x, y, z};
  // The following set comprehension picks all elements in s:
  var all := set o: object <- s;
  // The next set comprehension picks out 2 of the elements in s:
  var aa := set o: ClassA <- s;
  // The next set comprehension picks out the other 2 of the elements in s:
  var bb := set o: ClassB <- s;
  // The following picks out the same elements as in bb:
  var nn := set o: NothingInParticular <- s;

  print |s|, " ", |all|, " ";           // 4 4
  print |aa|, " ", |bb|, " ";           // 2 2
  print |aa * bb|, " ", |aa + bb|, " "; // 0 4
  print |nn|, " ", bb == nn, "\n";      // 2 true
}

// SetComprehension1 is like SetComprehension0, but also adds "null" to "s".
method SetComprehension1() {
  var w, x, y, z := new ClassA, new ClassA, new ClassB, new ClassB;
  var s := {w, x, y, z, null};
  // The following set comprehension picks all elements in s:
  var all := set o: object <- s;
  // The next set comprehension picks out 2 of the elements in s:
  var aa := set o: ClassA <- s;
  // The next set comprehension picks out the other 2 of the elements in s:
  var bb := set o: ClassB <- s;
  // The following picks out the same elements as in bb:
  var nn := set o: NothingInParticular <- s;

  print |s|, " ", |all|, " ";           // 5 4
  print |aa|, " ", |bb|, " ";           // 2 2
  print |aa * bb|, " ", |aa + bb|, " "; // 0 4
  print |nn|, " ", bb == nn, "\n";      // 2 true
}

// SetComprehension2 is like SetComprehension1, but uses maybe-null types in comprehensions
method SetComprehension2() {
  var w, x, y, z := new ClassA, new ClassA, new ClassB, new ClassB;
  var s := {w, x, y, z, null};
  // The following set comprehension picks all elements in s:
  var all := set o: object? <- s;
  // The next set comprehension picks out 2 of the elements in s:
  var aa := set o: ClassA? <- s;
  // The next set comprehension picks out the other 2 of the elements in s:
  var bb := set o: ClassB? <- s;
  // The following picks out the same elements as in bb:
  var nn := set o: NothingInParticular? <- s;

  print |s|, " ", |all|, " ";           // 5 5
  print |aa|, " ", |bb|, " ";           // 3 3
  print |aa * bb|, " ", |aa + bb|, " "; // 1 5
  print |nn|, " ", bb == nn, "\n";      // 3 true
}

datatype Color = Red | Green | Blue

predicate method True<G>(g: G) { true }

method SetComprehension3() {
  var s: set<bool> := {false, true};
  // The following set comprehension picks all elements in s:
  var all := set o: bool <- s;
  var aa := set o: bool <- s | !o;
  var bb := set o: bool <- s | o;

  print |s|, " ", |all|, " ";           // 2 2
  print |aa|, " ", |bb|, " ";           // 1 1
  print |aa * bb|, " ", |aa + bb|, " "; // 0 2
  print aa == all, " ", aa <= all, "\n"; // false true

  var d := set z: Color | True(z);
  var e := set z: Color | z in d;
  print |d|, " ", |e|, "\n"; // 3 3
}

trait ICell { var data: int }
class CellA extends ICell { }
class CellB extends ICell { }

method Enumerations() {
  var c, d, e := new CellA, new CellA, new CellB;
  c.data, d.data, e.data := 4, 5, 1;
  var s: set<ICell?> := {c, d, e, null};
  print c.data, d.data, e.data, "\n";  // 451

  // non-sequentialized forall statement
  forall a: CellA <- s {
    a.data := c.data + a.data - 2;
  }
  print c.data, d.data, e.data, "\n";  // 671

  // sequentialized forall statement
  forall a: CellA <- s {
    a.data := 2;
  }
  print c.data, d.data, e.data, "\n";  // 221

  // assign-such-that statement
  d.data := 9;
  assert d in s;
  var u: CellA :| u in s && 7 <= u.data;
  u.data := 8;
  print c.data, d.data, e.data, "\n";  // 281

  // set comprehension
  var r := set a: CellA <- s | a.data < 6;
  print |r|, "\n";  // 1

  // map comprehension
  var m := map a: CellA <- s | a.data < 6 :: 3;
  print c in m.Keys, " ", d in m.Keys, " ", |m.Keys|, "\n";  // true false 1
}

method EnumerationsMaybeNull() {
  var c, d, e := new CellA, new CellA, new CellB;
  c.data, d.data, e.data := 4, 5, 1;
  var s: set<ICell?> := {c, d, e, null};
  print c.data, d.data, e.data, "\n";  // 451

  // non-sequentialized forall statement
  forall a: CellA? <- s {
    (if a == null then c else a).data := c.data + (if a == null then c else a).data - 2;
  }
  print c.data, d.data, e.data, "\n";  // 671

  // sequentialized forall statement
  forall a: CellA? <- s {
    (if a == null then c else a).data := 2;
  }
  print c.data, d.data, e.data, "\n";  // 221

  // assign-such-that statement
  d.data := 9;
  assert d in s;
  var u: CellA? :| u in s && u != null && 7 <= u.data;
  u.data := 8;
  print c.data, d.data, e.data, "\n";  // 281

  // set comprehension
  var r := set a: CellA? <- s | (a == null || a.data < 6);
  print |r|, "\n";  // 2

  // map comprehension
  var m := map a: CellA? <- s | (a == null || a.data < 6) :: 3;
  print null in m.Keys, " ", c in m.Keys, " ", d in m.Keys, " ", |m.Keys|, "\n";  // true true false 2
}

module TestImplicitTypeTests {
  trait A {}
  trait B extends A {}
  class C extends B {}
  class A' extends A {}
  class B' extends B {}

  method Test() {
    var o, a, b, c := new object, new A', new B', new C;
    var r: set<object> := {o, a, b, c};
    var s: set<A> := set x: A <- r;
    var t: set<B> := set x: B <- s;
    var u: set<C> := set x: C <- s;
    print |r|, " ", |s|, " ", |t|, " ", |u|, "\n"; // 4 3 2 1
    print r == set x <- r | x is object, " "; // true
    print s == set x <- r | x is A, " "; // true
    print t == set x <- r | x is B, " "; // true
    print u == set x <- r | x is C, "\n"; // true

    var r': set<object?> := r;
    var s': set<A?> := s;
    var t': set<B?> := t;
    var u': set<C?> := u;
    print |r'|, " ", |s'|, " ", |t'|, " ", |u'|, "\n"; // 4 3 2 1
    print r' == set x <- r | x is object, " "; // true
    print s' == set x <- r | x is A, " "; // true
    print t' == set x <- r | x is B, " "; // true
    print u' == set x <- r | x is C, "\n"; // true

    r', s', t', u' := r' + {null}, s' + {null}, t' + {null}, u' + {null};
    print r' == set x <- r | x is object, " "; // false
    print s' == set x <- r | x is A, " "; // false
    print t' == set x <- r | x is B, " "; // false
    print u' == set x <- r | x is C, "\n"; // false
    print r' == set x <- r | x is object?, " "; // false
    print s' == set x <- r | x is A?, " "; // false
    print t' == set x <- r | x is B?, " "; // false
    print u' == set x <- r | x is C?, "\n"; // false

    print r == set x <- r' | x is object, " "; // true
    print s == set x <- r' | x is A, " "; // true
    print t == set x <- r' | x is B, " "; // true
    print u == set x <- r' | x is C, "\n"; // true
    print r == set x <- r' | x is object?, " "; // false
    print s == set x <- r' | x is A?, " "; // false
    print t == set x <- r' | x is B?, " "; // false
    print u == set x <- r' | x is C?, "\n"; // false
    print r == set x <- r' | x is object? && x != null, " "; // true
    print s == set x <- r' | x is A? && x != null, " "; // true
    print t == set x <- r' | x is B? && x != null, " "; // true
    print u == set x <- r' | x is C? && x != null, "\n"; // true
  }
}
