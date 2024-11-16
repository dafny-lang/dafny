module BoxLists {
  import opened Boxes
  import opened Lists
  import opened Order

  // A BoxList is a sorted list of Box'es without duplicates
  type BoxList = bxs: List<Box> | StrictlyIncreasing(bxs) witness Nil
  
  predicate StrictlyIncreasing(s: List<Box>) {
    forall i, j :: 0 <= i < j < s.Length() ==> Less(s.At(i), s.At(j))
  }

  lemma TailStrictlyIncreasing(s: List<Box>)
    requires StrictlyIncreasing(s) && s.Cons?
    ensures StrictlyIncreasing(s.tail)
  {
    assert forall i :: 0 <= i < s.tail.Length() ==> s.tail.At(i) == s.At(i + 1);
  }

  lemma PrependIncreasing(o: Box, s: List<Box>)
    requires StrictlyIncreasing(s)
    requires s != Nil && Less(o, s.head)
    ensures StrictlyIncreasing(Cons(o, s))
  {
    var r := Cons(o, s);
    forall i, j | 0 <= i < j < r.Length()
      ensures Less(r.At(i), r.At(j))
    {
      if i == 0 {
        var a, b, c := r.At(i), r.At(i + 1), r.At(j);
        assert a == o && b == s.At(i) && c == s.At(j - 1);
        if i + 1 == j {
        } else {
          assert Less(a, c) by {
            LessTransitive(a, b, c);
          }
        }
      }
    }
  }
}
