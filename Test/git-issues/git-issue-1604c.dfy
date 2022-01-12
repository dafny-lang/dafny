// RUN: %dafny /compile:3 /rprint:"%t.rprint" /compileTarget:js "%s" > "%t"
// RUN: %dafny /compile:3 /rprint:"%t.rprint" /compileTarget:java "%s" >> "%t"
// RUN: %dafny /compile:3 /rprint:"%t.rprint" /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:3 /rprint:"%t.rprint" /compileTarget:cs "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

trait Tr { }
class A extends Tr { }
class B extends Tr { }

predicate {:opaque} SpecialA(a: A) {
  true
}
type Ap  = x : A | SpecialA(x)

function method test(x: Tr): bool
  requires x is A
{
  if x is B then 1/0 == 0 else true
}
function method testSpecial(x: Tr): bool
  requires x is A && SpecialA(x)
{
  if x is B then 1/0 == 0 else true
}

method Main() {
  var a := new A;
  var b := new B;
  var s: set<Tr> := {a, b};
  var aa := forall a': A :: a' in s ==> test(a');
  var ap := forall a': Ap :: a' in s ==> test(a');
  assert(aa);
  assert(ap);
  print "ok";
}