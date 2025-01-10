// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

method Main() {
  M.TestTraits();
  M.TestConstraintsSimple();
  SimpleSetContainmentTests.Test();
}

module M {
  trait MyTrait extends object { }
  class MyClass extends MyTrait { }
  class AnotherClass extends MyTrait { }

  method TestTraits() {
    var c0 := new MyClass;
    var c1 := new AnotherClass;

    var s: set<MyClass> := {c0};
    var t := set x: MyTrait | x in s;
    expect t == {c0};

    var u: set<MyTrait> := {c0, c1};
    var v := set y: MyClass | y in u;
    expect v == {c0};

    var s': set<MyClass?> := {c0, null};
    var t' := set x: MyTrait | x in s';
    expect t' == {c0};

    var u': set<MyTrait?> := {c0, c1, null};
    var v' := set y: MyClass | y in u';
    expect v' == {c0};

    var s'': set<MyClass?> := {c0, null};
    var t'' := set x: MyTrait? | x in s'';
    expect t'' == s'';

    var u'': set<MyTrait?> := {c0, c1, null};
    var v'' := set y: MyClass? | y in u'';
    expect v'' == {null, c0};
  }

  type Not30 = x: int | x != 30
  newtype Not31 = x: int | x != 31

  predicate P<X>(x: X) { true }

  method TestConstraintsSimple() {
    var r0, r1;
    r0 := set a: Not30 | 29 <= a < 33 && P(a); // {29, 31, 32}
    r1 := set b: Not31 | 29 <= b < 33 && P(b); // {29, 30, 32}
    print |r0|, " ", |r1|, "\n"; // 3 3
  }
}

module SimpleSetContainmentTests {
  method Test() {
    M({}, {}, {}, null, null, null);
    N({}, {}, 2, 2);
  }

  trait MyTrait extends object { }
  class MyClass extends MyTrait { }

  method M(ss: set<MyTrait?>, oo: set<object?>, cc: set<MyClass?>, s: MyTrait?, o: object?, c: MyClass?) {
    var b: bool;

    b := s in ss;
    b := o in ss;
    b := c in ss;

    b := s in oo;
    b := o in oo;
    b := c in oo;

    b := s in cc;
    b := o in cc;
    b := c in cc;
  }

  method N(ii: set<int>, nn: set<nat>, i: int, n: nat) {
    var b: bool;

    b := i in ii;
    b := n in ii;

    b := i in nn;
    b := n in nn;
  }
}
