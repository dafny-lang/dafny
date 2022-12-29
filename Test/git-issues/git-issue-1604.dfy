// RUN: %baredafny run %args --target=js "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:1 /compileTarget:go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

trait Tr { }
class A extends Tr { }
class B extends Tr { }

predicate SpecialA(a: A)
{
  false
}
type Ap  = x : A | SpecialA(x) witness *

function method testSpecial(x: Tr): bool
  requires x is A && SpecialA(x)
{
  1/0 == 0
}

function method test(x: Tr): bool
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
