function bad(n: nat): nat
  decreases n;
{
  bad(n+1)
}
ghost method go_bad()
  ensures bad(0)==0;
{
}

datatype Nat = Zero | Succ(tail: Nat)
predicate ThProperty(step: nat, t: Nat, r: nat)
{
  match t
  case Zero => true
  case Succ(o) => step>0 && exists ro:nat :: ThProperty(step-1, o, ro)
}
ghost method test_ThProperty()
  ensures ThProperty(10, Succ(Zero), 0);
{
//  assert ThProperty(9, Zero, 0);
}