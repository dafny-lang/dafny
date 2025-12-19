// RUN: %exits-with 4 %verify --general-traits=datatype "%s" > "%t"
// RUN: %exits-with 4 %verify --general-traits=datatype --type-system-refresh "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"


trait Base {
  predicate Foo()
    decreases this

  predicate SomethingElse()
    decreases this, 55
  {
    true
  }
}

trait Extender extends Base {
  predicate Foo()
    // The following line once caused a crash in Dafny's new type system
    decreases this
}

class Class0 extends Base {
  predicate Foo()
    decreases this
  {
    SomethingElse() && Local() && true
  }

  predicate Local()
    decreases this, 55
  {
    true
  }
}

class Class1 extends Extender {
  predicate Foo()
    decreases this
  {
    SomethingElse() && Local() && false
  }

  predicate Local()
    decreases this, 55
  {
    true
  }
}

datatype Datatype0 extends Base = D0 {
  predicate Foo()
    decreases this
  {
    SomethingElse() && Local() && false
  }

  predicate Local()
    decreases this, 55
  {
    true
  }
}

datatype Datatype1 extends Extender = D1 {
  predicate Foo()
    decreases this
  {
    SomethingElse() && Local() && true
  }

  predicate Local()
    decreases this, 55
  {
    true
  }
}

method Main() {
  var c0: Class0 := new Class0;
  var c1: Class1 := new Class1;
  var d0: Datatype0 := D0;
  var d1: Datatype1 := D1;

  assert c0.Foo();
  assert !c1.Foo();
  assert !d0.Foo();
  assert d1.Foo();

  var b: Base := c1;
  var e: Extender := c1;
  assert !b.Foo() && !e.Foo();

  b, e := d1, d1;
  assert b.Foo() && e.Foo();

  assert b nonincreases to b;
  assert c0 nonincreases to c0;
  assert c0 decreases to null; // this picks the decreases metric for reference types
  assert b decreases to null; // error: from the static type of "b", this picks a generic decreases metric
}
