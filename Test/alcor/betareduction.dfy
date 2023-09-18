opaque function {:fuel 0, 0} f(x: int): int {
  if x <= 1 then x else f(x - 1) + f(x - 2)
}

lemma ComputeF() {
  assert f0: f(0) == 0 by {
    reveal f(), forall_elim(f, 0, r), recall(r);
  }
  assert f1: f(1) == 1 by {
    reveal f(), forall_elim(f, 1, r), recall(r);
  }
  assert f2: f(2) == 1 by {
    reveal f(), forall_elim(f, 2, r),
           definition(r, f0),
           definition(r, f1),
           recall(r);
  }
  assert f3: f(3) == 2 by {
    reveal f(), forall_elim(f, 3, r),
           definition(r, f2),
           definition(r, f1),
           recall(r);
  }
  assert f4: f(4) == 3 by {
    reveal f(), forall_elim(f, 4, r),
           definition(r, f3),
           definition(r, f2),
           recall(r);
  }
}

lemma ComputeF2()
{
  reveal f(),
         forall_elim(f, 2, f2),
         forall_elim(f, 1, f1),
         forall_elim(f, 0, f0),
         definition(f2, f1),
         definition(f2, f0),
         recall(f2);
  assert f(2) == 1;
}

method Test() {
  assert forall x :: f(x) == f(x);
}