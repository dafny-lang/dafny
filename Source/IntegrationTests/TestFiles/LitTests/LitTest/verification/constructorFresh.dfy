// RUN: ! %verify %s &> %t
// RUN: %diff "%s.expect" "%t"

class A {
  constructor()
}

class Test {

  var x: A

  constructor()
    ensures fresh(this.x)
    ensures foo()
  {
    x := new A();
  }
}

predicate foo()
  requires false
  ensures false 
{ true }

method Main() {
  var t := new Test();
  assert false;
}