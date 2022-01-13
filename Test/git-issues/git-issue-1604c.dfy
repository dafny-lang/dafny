// RUN: %dafny /compile:0 /rprint:"%t.rprint" /compileTarget:js "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
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

  // Fine because Ap has the same type as elements of s2
  var ab := forall a': Ap | a' in s2 :: testSpecial(a');
  assert aa;
  assert ab;
  print "ok";
}