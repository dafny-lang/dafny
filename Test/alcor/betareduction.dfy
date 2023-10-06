lemma TestExampleDafny3Tactic0()
{
  forall a, b | a || !a ensures a && b ==> a {
    if a && b {
      assert a;
    }
    assert a && b ==> a;
  }
  assert forall a, b | a || !a :: a && b ==> a;
}




lemma TestExampleDafny2Tactic1() {
  assert forall a, b :: a && b ==> a by {
    forall a, b ensures a && b ==> a {
      if a && b {
        reveal cases(h, hA, hB),
               recall(hA);
        assert a;
      }
    }
  }
}



lemma TestExampleDafny1Tactic2() {
  assert forall a, b :: a && b ==> a by {
    forall a, b ensures a && b ==> a {
      reveal intro(hAB),
             cases(hAB, hA, hB),
             recall(hA);
    }
  }
}
lemma TestExampleDafny0Tactic3() {
  reveal intro(),
         intro(),
         intro(hAB),
         cases(hAB, hA, hB),
         recall(hA);
  assert forall a, b :: a && b ==> a;
}





opaque function f(x: int): int {
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
    reveal f(),
           forall_elim(f, 2, r),
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
         forall_elim(f, 3, f3),
         forall_elim(f, 2, f2),
         definition(f3, f2),
         forall_elim(f, 1, f1),
         definition(f3, f1),
         forall_elim(f, 0, f0),
         definition(f3, f0),
         recall(f3);
  assert f(3) == 2;
}

