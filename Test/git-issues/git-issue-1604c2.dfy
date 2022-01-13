// RUN: %dafny /compile:3 /rprint:"%t.rprint" /compileTarget:js "%s" > "%t"
// RUN: %dafny /compile:3 /rprint:"%t.rprint" /compileTarget:java "%s" >> "%t"
// RUN: %dafny /compile:3 /rprint:"%t.rprint" /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:3 /rprint:"%t.rprint" /compileTarget:cs "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

trait Tr { }
class A extends Tr { }
class B extends Tr { }

// Abstract predicate cause errors at run-time so they should be caught
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

method Main() {
  var a := new A;
  var b := new B;
  var s: set<Tr> := {a, b};  
  // Resolution Error, because of subset type, need to use explicit range forall x | range :: term
  var ap := forall a': Ap :: a' in s ==> testSpecial(a');
  assert(ap);
  print "ok";
}