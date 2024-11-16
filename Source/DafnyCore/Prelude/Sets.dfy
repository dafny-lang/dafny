module {:extract_boogie} Sets {
  import opened Boxes
  import opened Lists

  // type Set = [Box]bool;
  // TODO: can this be a "newtype"? does it matter?
  // The manually authored Boogie type "Set" is defined as a Boogie map from Box to bool.
  // There was no strong reason for doing so. In fact, there are probably stronger reasons
  // to just define it as an uninterpreted type, which is what the effect of this
  // :extract_boogie_name annotation will have. See also the "In" predicate below.
  type {:extract_boogie_name "Set"} Set = s: List<Box> | StrictlyIncreasing(s) witness Nil
  
  predicate StrictlyIncreasing(s: List<Box>) {
    forall i, j :: 0 <= i < j < s.Length() ==> Less(s.At(i), s.At(j))
  }

  lemma TailStrictlyIncreasing(s: List<Box>)
    requires StrictlyIncreasing(s) && s.Cons?
    ensures StrictlyIncreasing(s.tail)
  {
    assert forall i :: 0 <= i < s.tail.Length() ==> s.tail.At(i) == s.At(i + 1);
  }

  // function Set#Card(Set): int;
  function {:extract_boogie_name "Set#Card"} Card(s: Set): int {
    s.Length()
  }

  // axiom (forall s: Set :: { Set#Card(s) } 0 <= Set#Card(s));
  lemma {:extract_pattern Card(s)} AboutCard(s: Set)
    ensures 0 <= Card(s)
  {
  }

  // function Set#Empty(): Set;
  function {:extract_boogie_name "Set#Empty"} Empty(): Set {
    Nil
  }

  // The manually written axioms use Boogie's built-in map selection operator, "_[_]",
  // for the following "In" predicate. There's no real advantage of using map selection
  // rather than a user-defined function, like the "In" here. In fact, by using the built-in
  // operator, one needs to show that the sets here are a conservative extension of
  // Boogie's maps, which is just extra work for no gain.
  predicate {:extract_boogie_name "[]"} In(s: List<Box>, o: Box) {
    s.Contains(o)
  }

  // axiom (forall o: Box :: { Set#Empty()[o] } !Set#Empty()[o]);
  lemma {:extract_pattern In(Empty(), o)} EmptyHasNoMembers(o: Box)
    ensures !In(Empty(), o)
  {
  }

  // axiom (forall s: Set :: { Set#Card(s) }
  //   (Set#Card(s) == 0 <==> s == Set#Empty()) &&
  //   (Set#Card(s) != 0 ==> (exists x: Box :: s[x])));
  lemma {:extract_pattern Card(s)} CardVsEmpty(s: Set)
    ensures Card(s) == 0 <==> s == Empty()
    ensures Card(s) != 0 ==> exists x: Box :: In(s, x)
  {
    if Card(s) == 0 {
      assert s == Empty();
    } else {
      assert s != Empty();
      assert In(s, s.head);
    }
  }

  // function Set#UnionOne(Set, Box): Set;
  function {:extract_boogie "Set#UnionOne"} UnionOne(s: Set, o: Box): Set {
    UnionOnePreservesStrictlyIncreasing(s, o);
    UnionOneRaw(s, o)
  }

  function UnionOneRaw(s: List<Box>, o: Box): List<Box> {
    match s
    case Nil => Cons(o, s)
    case Cons(x, tail) =>
      if o == x then
        s
      else if Less(o, x) then
        Cons(o, s)
      else
        Cons(x, UnionOneRaw(tail, o))
  }

  lemma UnionOneRawSame(s: List<Box>, o: Box)
    requires StrictlyIncreasing(s) && s.Contains(o)
    ensures s == UnionOneRaw(s, o)
  {
    if o == s.head {
    } else if Less(o, s.head) {
      assert false by {
        var i := s.tail.ContainsAt(o);
        assert o == s.tail.At(i) == s.At(i + 1);
        assert s.head == s.At(0);
        assert Less(s.head, s.At(i + 1));
        LessAsymmetric(o, s.head);
      }
    } else {
      UnionOneRawSame(s.tail, o) by {
        TailStrictlyIncreasing(s);
      }
    }
  }

  lemma UnionOnePreservesStrictlyIncreasing(s: List<Box>, o: Box)
    requires StrictlyIncreasing(s)
    ensures StrictlyIncreasing(UnionOneRaw(s, o))
  {
    var r := UnionOneRaw(s, o);
    match s
    case Nil =>
    case Cons(x, tail) =>
      if x == o { 
      } else if Less(o, x) {
        PrependIncreasing(o, s);
      } else {
        assert StrictlyIncreasing(tail) by {
          forall i, j | 0 <= i < j < tail.Length()
            ensures Less(tail.At(i), tail.At(j))
          {
            assert tail.At(i) == s.At(i + 1);
            assert tail.At(j) == s.At(j + 1);
          }
        }
        var r := UnionOneRaw(tail, o);
        assert StrictlyIncreasing(r) by {
          UnionOnePreservesStrictlyIncreasing(tail, o);
        }
        PrependIncreasing(x, r) by {
          assert r.head == o || r.head == tail.head;
          if r.head == o {
            assert Less(x, o) by {
              Total(o, x);
            }
          } else {
            assert x == s.At(0) && tail.head == s.At(1);
          }
        }
     }
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

  // axiom (forall a: Set, x: Box, o: Box :: { Set#UnionOne(a,x)[o] }
  //   Set#UnionOne(a,x)[o] <==> o == x || a[o]);
  lemma {:extract_pattern In(UnionOne(a, x), o)} UnionOneAddsElement(a: Set, x: Box, o: Box)
    ensures In(UnionOne(a, x), o) <==> o == x || In(a, o)
  {
    var b := UnionOne(a, x);
    match a
    case Nil =>
    case Cons(y, tail) =>
      if x == y {
        assert b == a;
      } else if Less(x, y) {
        assert b == Cons(x, a);
      } else {
        assert b == Cons(y, UnionOneRaw(tail, x));
        assert In(b, o) <==> o == y || In(UnionOneRaw(tail, x), o);
        if o == y {
        } else {
          calc {
            In(b, o);
            In(UnionOneRaw(tail, x), o);
            { TailStrictlyIncreasing(a); UnionOneAddsElement(tail, x, o); }
            o == x || In(tail, o);
            { assert y != o; assert In(tail, o) <==> In(a, o); }
            o == x || In(a, o);
          }
          
        }
      }
  }

  // axiom (forall a: Set, x: Box :: { Set#UnionOne(a, x) }
  //   Set#UnionOne(a, x)[x]);
  lemma {:extract_pattern UnionOne(a, x)} UnionOneAddsSelf(a: Set, x: Box)
    ensures In(UnionOne(a, x), x)
  {
    UnionOneAddsElement(a, x, x);
  }

  // axiom (forall a: Set, x: Box, y: Box :: { Set#UnionOne(a, x), a[y] }
  //   a[y] ==> Set#UnionOne(a, x)[y]);
  lemma {:extract_pattern UnionOne(a, x), In(a, y)} UnionOneMaintainsMembership(a: Set, x: Box, y: Box)
    requires In(a, y)
    ensures In(UnionOne(a, x), y)
  {
    UnionOneAddsElement(a, x, y);
  }

  // axiom (forall a: Set, x: Box :: { Set#Card(Set#UnionOne(a, x)) }
  //   a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a));
  lemma {:extract_pattern Card(UnionOne(a, x))} UnionOneCardIdempotent(a: Set, x: Box)
    requires In(a, x)
    ensures Card(UnionOne(a, x)) == Card(a)
  {
    assert Equal(UnionOne(a, x), a) by {
      forall o
        ensures In(UnionOne(a, x), o) <==> In(a, o)
      {
        UnionOneAddsElement(a, x, o);
      }
    }
    Extensionality(UnionOne(a, x), a);
  }

  // axiom (forall a: Set, x: Box :: { Set#Card(Set#UnionOne(a, x)) }
  //   !a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a) + 1);
  lemma {:extract_pattern Card(UnionOne(a, x))} CardUnionOne(a: Set, x: Box)
    requires !In(a, x)
    ensures Card(UnionOne(a, x)) == Card(a) + 1
  {
    match a
    case Nil =>
    case Cons(y, tail) =>
      if x == y {
        assert false; // by the assumption !In(a, x)
      } else if Less(x, y) {
      } else {
        TailStrictlyIncreasing(a);
        assert UnionOne(a, x) == Cons(y, UnionOne(tail, x));
        CardUnionOne(tail, x);
      }
  }

  // function Set#Union(Set, Set): Set;
  function {:extract_boogie_name "Set#Union"} Union(a: Set, b: Set): Set {
    match a
    case Nil => b
    case Cons(x, tail) =>
      TailStrictlyIncreasing(a);
      UnionOne(Union(tail, b), x)
  }

/*******************************
  function UnionAlt(a: List<Box>, b: List<Box>): List<Box> {
    match a
    case Nil => b
    case Cons(x, tail) =>
      if In(b, x) then
        UnionAlt(tail, b)
      else
        Cons(x, UnionAlt(tail, b))
  }

  lemma UnionAltElements(a: List<Box>, b: List<Box>, o: Box)
    ensures In(UnionAlt(a, b), o) <==> In(a, o) || In(b, o)
  {
  }

  lemma UnionAltPreservesStrictlyIncreasing(a: List<Box>, b: List<Box>)
    requires StrictlyIncreasing(a) && StrictlyIncreasing(b)
    ensures StrictlyIncreasing(UnionAlt(a, b))
  {
    match a
    case Nil =>
    case Cons(x, tail) =>
      TailStrictlyIncreasing(a);
      UnionAltPreservesStrictlyIncreasing(tail, b);
      if !In(b, x) {
        var c := UnionAlt(tail, b);
        assert UnionAlt(a, b) == Cons(x, c);
        forall o | In(c, o)
          ensures Less(x, o)
        {
          assert In(tail, o) || In(b, o) by {
            UnionAltElements(tail, b, o);
          }
          if In(tail, o) {
            var j := tail.ContainsAt(o);
            assert x == a.At(0) && o == a.At(j + 1);
          } else {
            var j := b.ContainsAt(o);
//            assert x == a.At(0) && o == 
          }
        }
        forall j | 0 <= j < c.Length()
          ensures Less(x, c.At(j))
        {
          c.AtContains(j, c.At(j));
        }
      }
  }

  lemma UnionSameAsUnionAlt(a: Set, b: Set)
    ensures Union(a, b) == UnionAlt(a, b)
  {
    forall o {
      calc {
        In(Union(a, b), o);
        { UnionElements(a, b, o); }
        In(a, o) || In(b, o);
        { UnionAltElements(a, b, o); }
        In(UnionAlt(a, b), o);
      }
    }
    assert StrictlyIncreasing(UnionAlt(a, b));
    Extensionality(Union(a, b), UnionAlt(a, b));
  }
*******************************/

  // axiom (forall a: Set, b: Set, o: Box :: { Set#Union(a,b)[o] }
  //   Set#Union(a,b)[o] <==> a[o] || b[o]);
  lemma {:extract_pattern In(Union(a, b), o)} UnionElements(a: Set, b: Set, o: Box)
    ensures In(Union(a, b), o) <==> In(a, o) || In(b, o)
  {
    match a
    case Nil =>
    case Cons(x, tail) =>
      TailStrictlyIncreasing(a);
      calc {
        In(Union(a, b), o);
        In(UnionOne(Union(tail, b), x), o);
        { UnionOneAddsElement(Union(tail, b), x, o); }
        o == x || In(Union(tail, b), o);
        { UnionElements(tail, b, o); }
        o == x || In(tail, o) || In(b, o);
        In(a, o) || In(b, o);
      }
  }

  // axiom (forall a, b: Set, y: Box :: { Set#Union(a, b), a[y] }
  //   a[y] ==> Set#Union(a, b)[y]);
  lemma {:extract_pattern In(Union(a, b), y)} UnionMonotonicA(a: Set, b: Set, y: Box)
    requires In(a, y)
    ensures In(Union(a, b), y)
  {
    UnionElements(a, b, y);
  }

  // axiom (forall a, b: Set, y: Box :: { Set#Union(a, b), b[y] }
  //   b[y] ==> Set#Union(a, b)[y]);
  lemma {:extract_pattern In(Union(a, b), y)} UnionMonotonicB(a: Set, b: Set, y: Box)
    requires In(b, y)
    ensures In(Union(a, b), y)
  {
    UnionElements(a, b, y);
  }

  lemma UnionCommutative(a: Set, b: Set)
    ensures Union(a, b) == Union(b, a)
  {
    forall o {
      calc {
        In(Union(a, b), o);
        { UnionElements(a, b, o); }
        In(a, o) || In(b, o);
        { UnionElements(b, a, o); }
        In(Union(b, a), o);
      }
    }
    Extensionality(Union(a, b), Union(b, a));
  }    

  // axiom (forall a, b: Set :: { Set#Union(a, b) }
  //   Set#Disjoint(a, b) ==>
  //     Set#Difference(Set#Union(a, b), a) == b &&
  //     Set#Difference(Set#Union(a, b), b) == a);
  // TODO
  // // Follows from the general union axiom, but might be still worth including, because disjoint union is a common case:
  // // axiom (forall a, b: Set :: { Set#Card(Set#Union(a, b)) }
  // //   Set#Disjoint(a, b) ==>
  // //     Set#Card(Set#Union(a, b)) == Set#Card(a) + Set#Card(b));

  // function Set#Intersection(Set, Set): Set;
  function {:extract_boogie_name "Set#Intersection"} Intersection(a: Set, b: Set): Set {
    IntersectionRawPreservesStrictlyIncreasing(a, b);
    IntersectionRaw(a, b)
  }

  function IntersectionRaw(a: List<Box>, b: List<Box>): List<Box> {
    match a
    case Nil => Nil
    case Cons(x, tail) =>
      if In(b, x) then
        Cons(x, IntersectionRaw(tail, b))
      else
        IntersectionRaw(tail, b)
  }

  lemma IntersectionRawElements(a: List<Box>, b: List<Box>, o: Box)
    ensures In(IntersectionRaw(a, b), o) <==> In(a, o) && In(b, o)
  {
  }

  lemma IntersectionRawPreservesStrictlyIncreasing(a: List<Box>, b: List<Box>)
    requires StrictlyIncreasing(a) && StrictlyIncreasing(b)
    ensures StrictlyIncreasing(IntersectionRaw(a, b))
  {
    match a
    case Nil =>
    case Cons(x, tail) =>
      TailStrictlyIncreasing(a);
      IntersectionRawPreservesStrictlyIncreasing(tail, b);
      if In(b, x) {
        var c := IntersectionRaw(tail, b);
        assert IntersectionRaw(a, b) == Cons(x, c);
        forall o | In(c, o)
          ensures Less(x, o)
        {
          assert In(tail, o) by {
            IntersectionRawElements(tail, b, o);
          }
          var j := tail.ContainsAt(o);
          assert x == a.At(0) && o == a.At(j + 1);
        }
        forall j | 0 <= j < c.Length()
          ensures Less(x, c.At(j))
        {
          c.AtContains(j, c.At(j));
        }
      }
  }

  // axiom (forall a: Set, b: Set, o: Box :: { Set#Intersection(a,b)[o] }
  //   Set#Intersection(a,b)[o] <==> a[o] && b[o]);
  lemma {:extract_pattern In(Intersection(a, b), o)} IntersectionElements(a: Set, b: Set, o: Box)
    ensures In(Intersection(a, b), o) <==> In(a, o) && In(b, o)
  {
    IntersectionRawElements(a, b, o);
  }

  lemma IntersectionCommutative(a: Set, b: Set)
    ensures Intersection(a, b) == Intersection(b, a)
  {
    forall o {
      calc {
        In(Intersection(a, b), o);
        { IntersectionElements(a, b, o); }
        In(a, o) && In(b, o);
        { IntersectionElements(b, a, o); }
        In(Intersection(b, a), o);
      }
    }
    Extensionality(Intersection(a, b), Intersection(b, a));
  }    

  // axiom (forall a, b: Set :: { Set#Union(Set#Union(a, b), b) }
  //   Set#Union(Set#Union(a, b), b) == Set#Union(a, b));
  lemma {:extract_pattern Union(Union(a, b), b)} UnionIdempotentB(a: Set, b: Set)
    ensures Union(Union(a, b), b) == Union(a, b)
  {
    forall o {
      calc {
        In(Union(Union(a, b), b), o);
        { UnionElements(Union(a, b), b, o); }
        In(Union(a, b), o) || In(b, o);
        { UnionElements(a, b, o); }
        In(a, o) || In(b, o) || In(b, o);
        In(a, o) || In(b, o);
        { UnionElements(a, b, o); }
        In(Union(a, b), o);
      }
    }
    Extensionality(Union(Union(a, b), b), Union(a, b));
  }

  // axiom (forall a, b: Set :: { Set#Union(a, Set#Union(a, b)) }
  //   Set#Union(a, Set#Union(a, b)) == Set#Union(a, b));
  lemma {:extract_pattern Union(a, Union(a, b))} UnionIdempotentA(a: Set, b: Set)
    ensures Union(a, Union(a, b)) == Union(a, b)
  {
    calc {
      Union(a, Union(a, b));
      { UnionCommutative(a, Union(a, b)); }
      Union(Union(a, b), a);
      { UnionCommutative(a, b); }
      Union(Union(b, a), a);
      { UnionIdempotentB(b, a); }
      Union(b, a);
      { UnionCommutative(a, b); }
      Union(a, b);
    }
  }

  // axiom (forall a, b: Set :: { Set#Intersection(Set#Intersection(a, b), b) }
  //   Set#Intersection(Set#Intersection(a, b), b) == Set#Intersection(a, b));
  lemma {:extract_pattern Intersection(Intersection(a, b), b)} IntersectionIdempotentB(a: Set, b: Set)
    ensures Intersection(Intersection(a, b), b) == Intersection(a, b)
  {
    forall o {
      calc {
        In(Intersection(Intersection(a, b), b), o);
        { IntersectionElements(Intersection(a, b), b, o); }
        In(Intersection(a, b), o) && In(b, o);
        { IntersectionElements(a, b, o); }
        In(a, o) && In(b, o) && In(b, o);
        In(a, o) && In(b, o);
        { IntersectionElements(a, b, o); }
        In(Intersection(a, b), o);
      }
    }
    Extensionality(Intersection(Intersection(a, b), b), Intersection(a, b));
  }

  // axiom (forall a, b: Set :: { Set#Intersection(a, Set#Intersection(a, b)) }
  //   Set#Intersection(a, Set#Intersection(a, b)) == Set#Intersection(a, b));
  lemma {:extract_pattern Intersection(a, Intersection(a, b))} IntersectionIdempotentA(a: Set, b: Set)
    ensures Intersection(a, Intersection(a, b)) == Intersection(a, b)
  {
    calc {
      Intersection(a, Intersection(a, b));
      { IntersectionCommutative(a, Intersection(a, b)); }
      Intersection(Intersection(a, b), a);
      { IntersectionCommutative(a, b); }
      Intersection(Intersection(b, a), a);
      { IntersectionIdempotentB(b, a); }
      Intersection(b, a);
      { IntersectionCommutative(a, b); }
      Intersection(a, b);
    }
  }

  lemma CardUnion(a: Set, b: Set)
    requires a != Nil
    ensures (TailStrictlyIncreasing(a);
      var m, n := Card(Union(a, b)), Card(Union(a.tail, b));
      m == if In(b, a.head) then n else n + 1)
  {
    TailStrictlyIncreasing(a);
    var Cons(x, tail) := a;
    var m, n := Card(Union(a, b)), Card(Union(tail, b));

    assert m == Card(UnionOne(Union(tail, b), x));
    assert !In(tail, x) by {
      TailDoesNotContainHead(a);
    }
    assert In(Union(tail, b), x) <==> In(b, x) by {
      assert In(Union(tail, b), x) <==> In(tail, x) || In(b, x) by {
        UnionElements(tail, b, x);
      }
    }
    if In(b, x) {
      assert In(Union(tail, b), x);
      assert m == n by {
        UnionOneCardIdempotent(Union(tail, b), x);
      }
    } else {
      assert m == n + 1 by {
        CardUnionOne(Union(tail, b), x);
      }
    }
  }

  // axiom (forall a, b: Set :: { Set#Card(Set#Union(a, b)) }{ Set#Card(Set#Intersection(a, b)) }
  //   Set#Card(Set#Union(a, b)) + Set#Card(Set#Intersection(a, b)) == Set#Card(a) + Set#Card(b));
  lemma {:extract_pattern Card(Union(a, b))} {:extract_pattern Card(Intersection(a, b))} CardUnionIntersection(a: Set, b: Set)
    ensures Card(Union(a, b)) + Card(Intersection(a, b)) == Card(a) + Card(b)
  {
    match a
    case Nil =>
    case Cons(x, tail) =>
      TailStrictlyIncreasing(a);
      var lhs0, lhs0' := Card(Union(a, b)), Card(Union(tail, b));
      assert lhs0 == if In(b, x) then lhs0' else lhs0' + 1 by {
        CardUnion(a, b);
      }

      var lhs1, lhs1' := Card(Intersection(a, b)), Card(Intersection(tail, b));
      assert lhs1 == if In(b, x) then lhs1' + 1 else lhs1';
  }

  // function Set#Difference(Set, Set): Set;
  function {:extract_boogie_name "Set#Difference"} Difference(a: Set, b: Set): Set {
    DifferenceRawPreservesStrictlyIncreasing(a, b);
    DifferenceRaw(a, b)
  }

  function DifferenceRaw(a: List<Box>, b: List<Box>): List<Box> {
    match a
    case Nil => Nil
    case Cons(x, tail) =>
      if In(b, x) then
        DifferenceRaw(tail, b)
      else
        Cons(x, DifferenceRaw(tail, b))
  }

  lemma DifferenceRawElements(a: List<Box>, b: List<Box>, o: Box)
    ensures In(DifferenceRaw(a, b), o) <==> In(a, o) && !In(b, o)
  {
  }

  lemma DifferenceRawPreservesStrictlyIncreasing(a: List<Box>, b: List<Box>)
    requires StrictlyIncreasing(a) && StrictlyIncreasing(b)
    ensures StrictlyIncreasing(DifferenceRaw(a, b))
  {
    match a
    case Nil =>
    case Cons(x, tail) =>
      TailStrictlyIncreasing(a);
      DifferenceRawPreservesStrictlyIncreasing(tail, b);
      if !In(b, x) {
        var c := DifferenceRaw(tail, b);
        assert DifferenceRaw(a, b) == Cons(x, c);
        forall o | In(c, o)
          ensures Less(x, o)
        {
          assert In(tail, o) by {
            DifferenceRawElements(tail, b, o);
          }
          var j := tail.ContainsAt(o);
          assert x == a.At(0) && o == a.At(j + 1);
        }
        forall j | 0 <= j < c.Length()
          ensures Less(x, c.At(j))
        {
          c.AtContains(j, c.At(j));
        }
      }
  }

  // axiom (forall a: Set, b: Set, o: Box :: { Set#Difference(a,b)[o] }
  //   Set#Difference(a,b)[o] <==> a[o] && !b[o]);
  lemma {:extract_pattern In(Difference(a, b), o)} DifferenceElements(a: Set, b: Set, o: Box)
    ensures In(Difference(a, b), o) <==> In(a, o) && !In(b, o)
  {
    DifferenceRawElements(a, b, o);
  }

  // axiom (forall a, b: Set, y: Box :: { Set#Difference(a, b), b[y] }
  //   b[y] ==> !Set#Difference(a, b)[y] );
  lemma {:extract_pattern Difference(a, b), In(b, y)} DifferenceSubtracts(a: Set, b: Set, y: Box)
    requires In(b, y)
    ensures !In(Difference(a, b), y)
  {
    calc {
      In(Difference(a, b), y);
      { DifferenceElements(a, b, y); }
      In(a, y) && !In(b, y);
      false;
    }
  }

  lemma CardOfDisjoint(a: Set, b: Set)
    requires Disjoint(a, b)
    ensures Card(Union(a, b)) == Card(a) + Card(b)
  {
    match a
    case Nil =>
    case Cons(x, tail) =>
      TailStrictlyIncreasing(a);
      var m, n := Card(Union(a, b)), Card(Union(a.tail, b));
      assert m == n + 1 by {
        CardUnion(a, b);
        assert !In(b, a.head);
      }
      CardOfDisjoint(tail, b);
  }

  // axiom (forall a, b: Set ::
  //   { Set#Card(Set#Difference(a, b)) }
  //   Set#Card(Set#Difference(a, b)) + Set#Card(Set#Difference(b, a))
  //   + Set#Card(Set#Intersection(a, b))
  //     == Set#Card(Set#Union(a, b)) &&
  //   Set#Card(Set#Difference(a, b)) == Set#Card(a) - Set#Card(Set#Intersection(a, b)));
  lemma {:extract_pattern Card(Difference(a, b))} CardDifference(a: Set, b: Set)
    ensures Card(Difference(a, b)) + Card(Difference(b, a)) + Card(Intersection(a, b)) == Card(Union(a, b))
    ensures Card(Difference(a, b)) == Card(a) - Card(Intersection(a, b))
  {
    var v, w := Difference(a, b), Difference(b, a);
    var i, u := Intersection(a, b), Union(a, b);

    assert L0: Union(Union(v, w), i) == u by {
      forall o {
        calc {
          In(Union(Union(v, w), i), o);
          { UnionElements(Union(v, w), i, o); }
          In(Union(v, w), o) || In(i, o);
          { UnionElements(v, w, o); }
          In(v, o) || In(w, o) || In(i, o);
          { DifferenceElements(a, b, o); DifferenceElements(b, a, o); IntersectionElements(a, b, o); }
          (In(a, o) && !In(b, o)) || (In(b, o) && !In(a, o)) || (In(a, o) && In(b, o));
          In(a, o) || In(b, o);
          { UnionElements(a, b, o); }
          In(u, o);
        }
      }
      Extensionality(Union(Union(v, w), i), u);
    }

    assert L1: Disjoint(Union(v, w), i) by {
      forall o {
        calc {
          In(Union(v, w), o);
          { UnionElements(v, w, o); }
          In(v, o) || In(w, o);
          { DifferenceElements(a, b, o); DifferenceElements(b, a, o); }
          (In(a, o) && !In(b, o)) || (In(b, o) && !In(a, o));
        ==>
          !(In(a, o) && In(b, o));
          { IntersectionElements(a, b, o); }
          !In(Intersection(a, b), o);
        }
      }
    }

    assert L2: Disjoint(v, w) by {
      forall o {
        calc {
          In(v, o);
          { DifferenceElements(a, b, o); }
          In(a, o) && !In(b, o);
        ==>
          !(In(b, o) && !In(a, o));
          { DifferenceElements(b, a, o); }
          !In(w, o);
        }
      }
    }

    assert M0: a == Union(v, i) by {
      forall o {
        calc {
          In(Union(v, i), o);
          { UnionElements(v, i, o); }
          In(v, o) || In(i, o);
          { DifferenceElements(a, b, o); IntersectionElements(a, b, o); }
          (In(a, o) && !In(b, o)) || (In(a, o) && In(b, o));
          In(a, o);
        }
      }
      Extensionality(a, Union(v, i));
    }

    assert M1: Disjoint(v, i) by {
      forall o {
        calc {
          In(v, o);
          { DifferenceElements(a, b, o); }
          In(a, o) && !In(b, o);
        ==>
          !(In(a, o) && In(b, o));
          { IntersectionElements(a, b, o); }
          !In(Intersection(a, b), o);
        }
      }
    }

    calc {
      Card(u);
      { reveal L0; }
      Card(Union(Union(v, w), i));
      { reveal L1; CardOfDisjoint(Union(v, w), i); }
      Card(Union(v, w)) + Card(i);
      { reveal L2; CardOfDisjoint(v, w); }
      Card(v) + Card(w) + Card(i);
    }

    calc {
      Card(a);
      { reveal M0; }
      Card(Union(v, i));
      { reveal M1; CardOfDisjoint(v, i); }
      Card(v) + Card(i);
    }
  }

  // function Set#Subset(Set, Set): bool;
  ghost predicate Subset(a: Set, b: Set) {
    forall o {:extract_pattern In(a, o)} {:extract_pattern In(b, o)} :: In(a, o) ==> In(b, o)
  }

  // axiom (forall a: Set, b: Set :: { Set#Subset(a,b) }
  //   Set#Subset(a,b) <==> (forall o: Box :: {a[o]} {b[o]} a[o] ==> b[o]));
  lemma {:extract_pattern Subset(a, b)} SubsetDefinition(a: Set, b: Set)
    ensures Subset(a, b) <==> forall o {:extract_pattern In(a, o)} {:extract_pattern In(b, o)} :: In(a, o) ==> In(b, o)
  {
  }

  // function Set#Equal(Set, Set): bool;
  ghost predicate {:extract_boogie_name "Seq#Equal"} Equal(a: Set, b: Set) {
    forall x :: In(a, x) <==> In(b, x)
  }

  // axiom (forall a: Set, b: Set :: { Set#Equal(a,b) }
  //   Set#Equal(a,b) <==> (forall o: Box :: {a[o]} {b[o]} a[o] <==> b[o]));
  lemma {:extract_pattern Equal(a, b)} EqualDefinition(a: Set, b: Set)
    ensures Equal(a, b) <==> forall o {:extract_pattern In(a, o)} {:extract_pattern In(b, o)} :: In(a, o) <==> In(b, o)
  {
  }

  // axiom (forall a: Set, b: Set :: { Set#Equal(a,b) }  // extensionality axiom for sets
  //   Set#Equal(a,b) ==> a == b);
  lemma Extensionality(a: Set, b: Set)
    requires Equal(a, b)
    ensures a == b
  {
    match a
    case Nil =>
      assert a == Empty();
      forall o
        ensures !In(b, o)
      {
        EmptyHasNoMembers(o);
      }
      CardVsEmpty(b);
    case Cons(x, tail) =>
      forall o | Less(o, x)
        ensures !In(a, o)
      {
        NothingIsSmallerThanHead(a, o);
      }
      assert In(b, x);
      assert b.head == x by {
        assert Below(b.head, x) by {
          HeadIsSmallest(b, x);
        }
        assert !Less(b.head, x);
      }
      assert b.tail == tail by {
        forall o
          ensures In(a.tail, o) <==> In(b.tail, o)
        {
          calc {
            In(a.tail, o);
            { TailDoesNotContainHead(a); }
            In(a.tail, o) && a.head != o;
            In(a, o) && a.head != o;
            In(b, o) && b.head != o;
            In(b.tail, o) && b.head != o;
            { TailDoesNotContainHead(b); }
            In(b.tail, o);
          }
        }
        TailStrictlyIncreasing(a);
        TailStrictlyIncreasing(b);
        Extensionality(tail, b.tail);
      }
  }

  lemma HeadIsSmallest(s: List<Box>, o: Box)
    requires StrictlyIncreasing(s) && s.Contains(o)
    ensures Below(s.head, o)
  {
    if o == s.head {
      Reflexive(o);
    } else {
      var j := s.ContainsAt(o);
      assert s.head == s.At(0) && o == s.At(j);
      assert Less(s.head, o);
    }
  }

  lemma NothingIsSmallerThanHead(s: List<Box>, o: Box)
    requires StrictlyIncreasing(s) && s != Nil && Less(o, s.head)
    ensures !s.Contains(o)
  {
    if s.Contains(o) {
      HeadIsSmallest(s, o);
      assert Below(s.head, o);
      LessBelowAsymmetric(o, s.head);
      assert false;
    }
  }

  lemma TailDoesNotContainHead(s: List<Box>)
    requires StrictlyIncreasing(s) && s != Nil
    ensures !s.tail.Contains(s.head)
  {
    if s.tail.Contains(s.head) {
      assert s.At(0) == s.head;
      var j := s.tail.ContainsAt(s.head);
      assert s.At(j + 1) == s.head;
      assert Less(s.At(0), s.At(j + 1));
      assert false;
    }
  }

  // function Set#Disjoint(Set, Set): bool;
  ghost predicate {:extract_boogie_name "Set#Disjoint"} Disjoint(a: Set, b: Set) {
    forall o {:extract_pattern In(a, o)} {:extract_pattern In(b, o)} :: !In(a, o) || !In(b, o)
  }

  // axiom (forall a: Set, b: Set :: { Set#Disjoint(a,b) }
  //   Set#Disjoint(a,b) <==> (forall o: Box :: {a[o]} {b[o]} !a[o] || !b[o]));
  lemma {:extract_pattern Disjoint(a, b)} DisjointDefinition(a: Set, b: Set)
    ensures Disjoint(a, b) <==> forall o {:extract_pattern In(a, o)} {:extract_pattern In(b, o)} :: !In(a, o) || !In(b, o)
  {
  }

}
  // // the empty set could be of anything
  // //axiom (forall t: Ty :: { $Is(Set#Empty() : [Box]bool, TSet(t)) } $Is(Set#Empty() : [Box]bool, TSet(t)));

  // NOT USED:
  // function Set#Singleton(Box): Set;
  // axiom (forall r: Box :: { Set#Singleton(r) } Set#Singleton(r)[r]);
  // axiom (forall r: Box, o: Box :: { Set#Singleton(r)[o] } Set#Singleton(r)[o] <==> r == o);
  // axiom (forall r: Box :: { Set#Card(Set#Singleton(r)) } Set#Card(Set#Singleton(r)) == 1);

  // // axiom(forall a: Set, b: Set ::
  // //   { Set#Subset(a,b), Set#Card(a), Set#Card(b) }  // very restrictive trigger
  // //   Set#Subset(a,b) ==> Set#Card(a) <= Set#Card(b));
