// RUN: %testDafnyForEachCompiler "%s"

trait Tr extends object { }
class A extends Tr { }
class B extends Tr { }

ghost predicate SpecialA(a: A)
{
  false
}
type Ap  = x : A | SpecialA(x) witness *

function testSpecial(x: Tr): bool
  requires x is A && SpecialA(x as A)
{
  1/0 == 0
}

function test(x: Tr): bool
  requires x is A
{
  if x is B then 1/0 == 0 else true
}

method Main() {
  var a := new A;
  var b := new B;
  var s: set<Tr> := {a, b};
  var s2: set<Ap> := {};
  var aa := forall a': A :: a' in s ==> test(a');

  // No way to make any of these work, for now ?
  //ab := forall a': Ap :: !testSpecial(a') ==> !(a' in s2);
  //ab := forall a': Ap :: a' in s2 ==> testSpecial(a');

  var si: set<int> := {2, 3, 4};
  var ai:= forall i: nat :: i in si ==> i > 1;

  assert aa;
  print "ok";
}
