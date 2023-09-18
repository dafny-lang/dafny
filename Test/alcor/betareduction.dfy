opaque function f(x: int): int {
  if x <= 1 then x else f(x - 1) + f(x - 2)
}

lemma ComputeF()
{
  reveal f(),
         rename(f, fdef),
         forall_elim(fdef, 2, f2),
         simplify(f2),
         forall_elim(fdef, 1, f1),
         simplify(f1),
         forall_elim(fdef, 0, f0),
         simplify(f0),
         definition(f2, f1),
         definition(f2, f0),
         recall(f2);
  assert f(2) == 1;
}

method Test() {
  assert forall x :: f(x) == f(x);
}