// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function bad(n: nat): nat
  decreases n
{
  bad(n+1)  // error: termination failure
}
ghost method go_bad()
  ensures bad(0)==0
{  // error: postcondition violation
}

datatype Nat = Zero | Succ(tail: Nat)
predicate ThProperty(step: nat, t: Nat, r: nat)
{
  match t
  case Zero => true
  case Succ(o) => step>0 && exists ro:nat, ss :: ss == step-1 && ThProperty(ss, o, ro) // WISH: auto-generate ss
}
ghost method test_ThProperty()
  ensures ThProperty(10, Succ(Zero), 0)
{  // error: postcondition violation
//  assert ThProperty(9, Zero, 0);
}

// The following is a test that well-typedness antecednets are included in the literal axioms
function StaticFact(n: nat): nat
  ensures 0 < StaticFact(n)
{
  if n == 0 then 1 else n * StaticFact(n - 1)
}
method test_StaticFact()
{
  assert StaticFact(0) == 1;
  assert 42 != 42;  // error:  this should fail
}
function fact(n: nat): nat
{
  if (n==0) then 1 else n*fact(n-1)
}
method test_fact()
{
  assert fact(0) == 1;
  assert 42 != 42;  // error:  this should fail
}
