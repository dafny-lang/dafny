module {:extract_boogie} Multisets {
  import opened Boxes
  import opened Lists
  import Math
  import Sets`Friends
  import Sequences`Friends

  // type MultiSet = [Box]int;
  // The manually authored Boogie type "MultiSet" is defined as a Boogie map from Box to int.
  // The reason for doing so was to obtain the Boogie map-update operation for free (in addition
  // to the map-select operation, of course). However, there are probably stronger reasons
  // to just define it as an uninterpreted type, which is what the effect of this
  // :extract_boogie_name annotation will have. Instead of Boogie's map-select and map-udate operators,
  // the model here uses functions Multiplicity and UpdateMultiplicity, respectively.
  // See also Sets.dfy and the "IsMember" predicate in that file.
  type {:extract_boogie_name "MultiSet"} Multiset = m: List<Box> | Increasing(m) witness Nil

  predicate Increasing(m: List<Box>) {
    forall i, j :: 0 <= i < j < m.Length() ==> Below(m.At(i), m.At(j))
  }

  lemma TailIncreasing(s: List<Box>)
    requires Increasing(s) && s.Cons?
    ensures Increasing(s.tail)
  {
    assert forall i :: 0 <= i < s.tail.Length() ==> s.tail.At(i) == s.At(i + 1);
  }

  function {:extract_boogie_name "MultiSet#Multiplicity"} Multiplicity(m: Multiset, o: Box): int {
    match m
    case Nil => 0
    case Cons(x, tail) =>
      TailIncreasing(m);
      BoolInt(x == o) + Multiplicity(tail, o)
  }

  function BoolInt(b: bool): nat {
    if b then 1 else 0
  }

  function {:extract_boogie_name "MultiSet#UpdateMultiplicity"} UpdateMultiplicity(m: Multiset, o: Box, n: int): Multiset
  {
    if n < 0 then m else
    UpdatePreservesIncreasing(m, o, n);
    Update(m, o, n)
  }

  function Update(m: List<Box>, o: Box, n: nat): List<Box>
  {
    if m.Cons? && Less(m.head, o) then
      Cons(m.head, Update(m.tail, o, n))
    else if n != 0 then
      Cons(o, Update(m, o, n - 1))
    else if m == Nil then
      Nil
    else if m.head == o then
      Update(m.tail, o, 0)
    else
      m
  }

  lemma {:extract_pattern Multiplicity(UpdateMultiplicity(m, o, n), p)} SelectOfUpdate(m: Multiset, o: Box, n: int, p: Box)
    requires 0 <= n
    ensures o == p ==> Multiplicity(UpdateMultiplicity(m, o, n), p) == n
    ensures o != p ==> Multiplicity(UpdateMultiplicity(m, o, n), p) == Multiplicity(m, p)
  {
    if o == p {
      MultiplicityUpdateSame(m, o, n);
    } else {
      MultiplicityUpdateDifferent(m, o, n, p);
    }
  }

  lemma MultiplicityUpdateSame(m: Multiset, o: Box, n: int)
    requires 0 <= n
    ensures (UpdatePreservesIncreasing(m, o, n);
             Multiplicity(Update(m, o, n), o) == n)
  {
    var u := Update(m, o, n);
    UpdatePreservesIncreasing(m, o, n);
    if m.Cons? && Less(m.head, o) {
      assert u == Cons(m.head, Update(m.tail, o, n));
      TailIncreasing(m);
    } else if n != 0 {
      assert u == Cons(o, Update(m, o, n - 1));
      UpdatePreservesIncreasing(m, o, n - 1);
    } else if m == Nil {
      assert u == Nil;
    } else if m.head == o {
      assert u == Update(m.tail, o, 0);
      calc {
        Multiplicity(u, o);
        Multiplicity(Update(m.tail, o, 0), o);
        { TailIncreasing(m); MultiplicityUpdateSame(m.tail, o, 0); }
        0;
      }
    } else {
      assert u == m;
      assert m.Cons? && m.head != o;
      assert !Less(m.head, o);
      assert Less(o, m.head) by {
        Connected(m.head, o);
      }
      ZeroMultiplicityForLargerElements(m, o);
    }
  }

  lemma MultiplicityUpdateDifferent(m: Multiset, o: Box, n: int, p: Box)
    requires 0 <= n && o != p
    ensures (UpdatePreservesIncreasing(m, o, n);
             Multiplicity(Update(m, o, n), p) == Multiplicity(m, p))
  {
    var u := Update(m, o, n);
    UpdatePreservesIncreasing(m, o, n);
    if m.Cons? && Less(m.head, o) {
      assert u == Cons(m.head, Update(m.tail, o, n));
      TailIncreasing(m);
    } else if n != 0 {
      assert u == Cons(o, Update(m, o, n - 1));
      UpdatePreservesIncreasing(m, o, n - 1);
    } else if m == Nil {
      assert u == Nil;
    } else if m.head == o {
      assert u == Update(m.tail, o, 0);
      calc {
        Multiplicity(u, p);
        Multiplicity(Update(m.tail, o, 0), p);
        { TailIncreasing(m); MultiplicityUpdateDifferent(m.tail, o, 0, p); }
        Multiplicity(m.tail, p);
      }
    } else {
      assert u == m;
    }
  }

  lemma ElementsOfUpdate(m: List<Box>, o: Box, n: nat, m': List<Box>)
    requires m' == Update(m, o, n)
    ensures forall i :: 0 <= i < m'.Length() ==> m'.At(i) == o || m.Contains(m'.At(i))
  {
    forall i | 0 <= i < m.Length() {
      m.AtContains(i, m.At(i));
    }
  }

  lemma HeadIsLeast(x: Box, m: List<Box>)
    requires Increasing(m)
    requires m == Nil || Below(x, m.head)
    ensures forall i :: 0 <= i < m.Length() ==> Below(x, m.At(i))
  {
    forall i | 1 <= i < m.Length()
      ensures Below(x, m.At(i))
    {
      Transitive(x, m.At(0), m.At(i));
    }
  }

  lemma ConsUpdatePreservesIncreasing(x: Box, m: List<Box>, o: Box, n: nat)
    requires Increasing(m)
    requires Increasing(Update(m, o, n))
    requires forall i :: 0 <= i < m.Length() ==> Below(x, m.At(i))
    requires Below(x, o)
    ensures Increasing(Cons(x, Update(m, o, n)))
  {
    var m1 := Update(m, o, n);
    var m' := Cons(x, m1);

    assert Increasing(m') by {
      PrependPreservesIncreasingAll(x, m1) by {
        forall i | 0 <= i < m1.Length()
          ensures Below(x, m1.At(i))
        {
          ElementsOfUpdate(m, o, n, m1);
          if m1.At(i) != o {
            var j := m.ContainsAt(m1.At(i));
            assert m1.At(i) == m.At(j);
            if j == 0 {
              assert m.At(j) == m.head;
            } else {
              assert Below(x, m.At(j)) by {
                Transitive(x, m.At(0), m.At(j));
              }
            }
          }
        }
    }
    }
  }

  lemma UpdatePreservesIncreasing(m: List<Box>, o: Box, n: nat)
    requires Increasing(m)
    ensures Increasing(Update(m, o, n))
  {
    var m' := Update(m, o, n);
    if m.Cons? && Less(m.head, o) {
      assert m' == Cons(m.head, Update(m.tail, o, n));
      TailIncreasing(m);
      m.HeadTailAt();
      ConsUpdatePreservesIncreasing(m.head, m.tail, o, n);

    } else if n != 0 {
      assert m' == Cons(o, Update(m, o, n - 1));
      Reflexive(o);
      assert m == Nil || Below(o, m.head) by {
        if m != Nil {
          NotLess(m.head, o);
        }
      }
      HeadIsLeast(o, m);
      ConsUpdatePreservesIncreasing(o, m, o, n - 1);

    } else if m == Nil {
      assert m' == Nil;

    } else if m.head == o {
      assert m' == Update(m.tail, o, n);
      TailIncreasing(m);

    } else {
      assert m' == m;
    }
  }

  lemma PrependPreservesIncreasingAll(o: Box, m: List<Box>)
    requires Increasing(m)
    requires forall i :: 0 <= i < m.Length() ==> Below(o, m.At(i))
    ensures Increasing(Cons(o, m))
  {
  }

  lemma PrependPreservesIncreasing(o: Box, m: List<Box>)
    requires Increasing(m)
    requires m == Nil || Below(o, m.head)
    ensures Increasing(Cons(o, m))
  {
    if m != Nil {
      PrependPreservesIncreasingAll(o, m) by {
        forall i | 0 <= i < m.Length()
          ensures Below(o, m.At(i))
        {
          assert Below(o, m.At(i)) by {
            Reflexive(m.At(0));
            Transitive(o, m.At(0), m.At(i));
          }
        }
      }
    }
  }

  // function $IsGoodMultiSet(ms: MultiSet): bool;
  predicate {:extract_boogie_name "$IsGoodMultiSet"} IsGood(ms: Multiset) {
    true
  }

  // // ints are non-negative, used after havocing, and for conversion from sequences to multisets.
  // axiom (forall ms: MultiSet :: { $IsGoodMultiSet(ms) }
  //   $IsGoodMultiSet(ms) <==>
  //   (forall bx: Box :: { ms[bx] } 0 <= ms[bx] && ms[bx] <= MultiSet#Card(ms)));
  lemma {:extract_pattern IsGood(ms)} GoodDefinition(ms: Multiset)
    ensures IsGood(ms) <==> forall bx {:extract_pattern Multiplicity(ms, bx)} :: 0 <= Multiplicity(ms, bx) && Multiplicity(ms, bx) <= Card(ms)
  {
    forall bx {
      MultiplicityCard(ms, bx);
    }
  }

  lemma MultiplicityCard(m: Multiset, x: Box)
    ensures 0 <= Multiplicity(m, x) <= Card(m)
  {
    match m
    case Nil =>
    case Cons(y, tail) =>
      TailIncreasing(m);
  }

  // function MultiSet#Card(MultiSet): int;
  function {:extract_boogie_name "MultiSet#Card"} Card(m: Multiset): int {
    m.Length()
  }

  // axiom (forall s: MultiSet :: { MultiSet#Card(s) } 0 <= MultiSet#Card(s));
  lemma {:extract_pattern Card(s)} AboutCard(s: Multiset)
    ensures 0 <= Card(s)
  {
  }

  // axiom (forall s: MultiSet, x: Box, n: int :: { MultiSet#Card(s[x := n]) }
  //   0 <= n ==> MultiSet#Card(s[x := n]) == MultiSet#Card(s) - s[x] + n);
  lemma {:extract_pattern Card(UpdateMultiplicity(s, x, n))} CardUpdate(s: Multiset, x: Box, n: int)
    requires 0 <= n
    ensures Card(UpdateMultiplicity(s, x, n)) == Card(s) - Multiplicity(s, x) + n
  {
    var u := UpdateMultiplicity(s, x, n);
    if s.Cons? && Less(s.head, x) {
      assert u == Cons(s.head, Update(s.tail, x, n));
      calc {
        Card(u);
        Card(Cons(s.head, Update(s.tail, x, n)));
        { TailIncreasing(s); }
        Card(Cons(s.head, UpdateMultiplicity(s.tail, x, n)));
        1 + Card(UpdateMultiplicity(s.tail, x, n));
        { CardUpdate(s.tail, x, n); }
        1 + Card(s.tail) - Multiplicity(s.tail, x) + n;
        Card(s) - Multiplicity(s.tail, x) + n;
      }

    } else if n != 0 {
      assert u == Cons(x, Update(s, x, n - 1));
      calc {
        Card(u);
        Card(Cons(x, Update(s, x, n - 1)));
        Card(Cons(x, UpdateMultiplicity(s, x, n - 1)));
        1 + Card(UpdateMultiplicity(s, x, n - 1));
        { CardUpdate(s, x, n - 1); }
        1 + Card(s) - Multiplicity(s, x) + n - 1;
      }

    } else if s == Nil {
      assert u == Nil;

    } else if s.head == x {
      assert u == Update(s.tail, x, 0);
      calc {
        Card(u);
        Card(Update(s.tail, x, 0));
        { TailIncreasing(s); }
        Card(UpdateMultiplicity(s.tail, x, 0));
        { CardUpdate(s.tail, x, 0); }
        Card(s.tail) - Multiplicity(s.tail, x) + n;
        { assert Card(s) == 1 + Card(s.tail); }
        Card(s) - 1 - Multiplicity(s.tail, x) + n;
      }

    } else {
      assert u == s;
      assert s.Cons? && s.head != x;
      assert !Less(s.head, x);
      assert Less(x, s.head) by {
        Connected(s.head, x);
      }
      ZeroMultiplicityForLargerElements(s, x);
    }
  }

  lemma ZeroMultiplicityForLargerElements(s: Multiset, x: Box)
    requires s == Nil || Less(x, s.head)
    ensures Multiplicity(s, x) == 0
  {
    match s
    case Nil =>
    case Cons(y, tail) =>
      TailIncreasing(s);
      if tail != Nil {
        assert Less(x, s.At(0)) && Below(s.At(0), s.At(1));
        LessBelowTransitive(x, s.At(0), s.At(1));
      }
      ZeroMultiplicityForLargerElements(tail, x);
  }

  lemma ZeroMultiplicityForNonElements(s: Multiset, o: Box)
    requires !s.Contains(o)
    ensures Multiplicity(s, o) == 0
  {
    NonZeroMultiplicityForElements(s, o);
  }

  lemma NonZeroMultiplicityForElements(s: Multiset, o: Box)
    ensures s.Contains(o) <==> Multiplicity(s, o) != 0
  {
    match s
    case Nil =>
    case Cons(x, tail) =>
      TailIncreasing(s);
      assert Multiplicity(s, o) == BoolInt(x == o) + Multiplicity(tail, o);
      if x == o {
        MultiplicityCard(tail, o);
      } else {
        NonZeroMultiplicityForElements(tail, o);
      }
  }

  // function MultiSet#Empty(): MultiSet;
  function {:extract_boogie_name "MultiSet#Empty"} Empty(): Multiset {
    Nil
  }

  // axiom (forall o: Box :: { MultiSet#Empty()[o] } MultiSet#Empty()[o] == 0);
  lemma {:extract_pattern Multiplicity(Empty(), o)} EmptyMultiplicities(o: Box)
    ensures Multiplicity(Empty(), o) == 0
  {
  }

  // axiom (forall s: MultiSet :: { MultiSet#Card(s) }
  //   (MultiSet#Card(s) == 0 <==> s == MultiSet#Empty()) &&
  //   (MultiSet#Card(s) != 0 ==> (exists x: Box :: 0 < s[x])));
  lemma {:extract_pattern Card(s)} CardVsEmpty(s: Multiset)
    ensures Card(s) == 0 <==> s == Empty()
    ensures Card(s) != 0 ==> exists x {:extract_pattern Multiplicity(s, x)} :: 0 < Multiplicity(s, x)
  {
    if Card(s) != 0 {
      assert s.Cons?;
      calc {
        Multiplicity(s, s.head);
      ==  { TailIncreasing(s); }
        1 + Multiplicity(s.tail, s.head);
      >  { MultiplicityCard(s.tail, s.head); }
        0;
      }
    }
  }

  // function MultiSet#Singleton(Box): MultiSet;
  function {:extract_boogie_name "MultiSet#Singleton"} Singleton(o: Box): Multiset {
    var singleton := Cons(o, Nil);
    assert singleton.Length() == 1;
    singleton
  }

  // axiom (forall r: Box, o: Box :: { MultiSet#Singleton(r)[o] } (MultiSet#Singleton(r)[o] == 1 <==> r == o) &&
  //                                                             (MultiSet#Singleton(r)[o] == 0 <==> r != o));
  lemma {:extract_pattern Multiplicity(Singleton(r), o)} AboutSingleton(r: Box, o: Box)
    ensures Multiplicity(Singleton(r), o) == 1 <==> r == o
    ensures Multiplicity(Singleton(r), o) == 0 <==> r != o
  {
  }

  // axiom (forall r: Box :: { MultiSet#Singleton(r) } MultiSet#Singleton(r) == MultiSet#UnionOne(MultiSet#Empty(), r));
  lemma {:extract_pattern Singleton(r)} SingletonUnionOne(r: Box)
    ensures Singleton(r) == UnionOne(Empty(), r)
  {
  }

  // function MultiSet#UnionOne(MultiSet, Box): MultiSet;
  function {:extract_boogie_name "MultiSet#UnionOne"} UnionOne(m: Multiset, o: Box): Multiset
    ensures UnionOne(m, o).Cons?
    decreases m, 0
  {
    if m.Cons? && Less(m.head, o) then
      TailIncreasing(m);
      var m' := UnionOne(m.tail, o);
      assert Below(m.head, m'.head) by {
        if m'.head != o {
          assert m.head == m.At(0);
          assert m'.head == m.tail.head == m.At(1);
        }
      }
      PrependPreservesIncreasing(m.head, m');
      Cons(m.head, m')
    else
      assert m == Nil || Below(o, m.head) by {
        if m != Nil {
          NotLess(m.head, o);
        }
      }
      PrependPreservesIncreasing(o, m);
      Cons(o, m)
  }

  // // pure containment axiom (in the original multiset or is the added element)
  // axiom (forall a: MultiSet, x: Box, o: Box :: { MultiSet#UnionOne(a,x)[o] }
  //   0 < MultiSet#UnionOne(a,x)[o] <==> o == x || 0 < a[o]);
  lemma {:extract_pattern Multiplicity(UnionOne(a, x), o)} PureContainment(a: Multiset, x: Box, o: Box)
    ensures 0 < Multiplicity(UnionOne(a, x), o) <==> o == x || 0 < Multiplicity(a, o)
  {
    MultiplicityDelta(a, x, o);
    MultiplicityCard(a, x);
  }

  lemma UnionOneContains(a: Multiset, x: Box, o: Box)
    ensures UnionOne(a, x).Contains(o) <==> o == x || a.Contains(o)
  {
    calc {
      UnionOne(a, x).Contains(o);
      {  NonZeroMultiplicityForElements(UnionOne(a, x), o); }
      Multiplicity(UnionOne(a, x), o) != 0;
      { MultiplicityCard(UnionOne(a, x), o); }
      0 < Multiplicity(UnionOne(a, x), o);
      { PureContainment(a, x, o); }
      o == x || 0 < Multiplicity(a, o);
      { MultiplicityCard(a, o); }
      o == x || Multiplicity(a, o) != 0;
      { NonZeroMultiplicityForElements(a, o); }
      o == x || a.Contains(o);
    }
  }

  // // union-ing increases count by one
  // axiom (forall a: MultiSet, x: Box :: { MultiSet#UnionOne(a, x) }
  //   MultiSet#UnionOne(a, x)[x] == a[x] + 1);
  lemma {:extract_pattern UnionOne(a, x)} MultiplicityUnionOne(a: Multiset, x: Box)
    ensures Multiplicity(UnionOne(a, x), x) == Multiplicity(a, x) + 1
  {
    if a.Cons? {
      TailIncreasing(a);
    }
  }

  lemma MultiplicityDelta(a: Multiset, x: Box, y: Box)
    ensures Multiplicity(UnionOne(a, x), y) == BoolInt(x == y) + Multiplicity(a, y)
  {
    if x == y {
      MultiplicityUnionOne(a, y);
    } else {
      OtherElementsUnchanged(a, x, y);
    }
  }

  // // non-decreasing
  // axiom (forall a: MultiSet, x: Box, y: Box :: { MultiSet#UnionOne(a, x), a[y] }
  //   0 < a[y] ==> 0 < MultiSet#UnionOne(a, x)[y]);
  lemma {:extract_pattern UnionOne(a, x), Multiplicity(a, y)} NonDecreasing(a: Multiset, x: Box, y: Box)
    requires 0 < Multiplicity(a, y)
    ensures 0 < Multiplicity(UnionOne(a, x), y)
  {
    MultiplicityDelta(a, x, y);
  }

  // // other elements unchanged
  // axiom (forall a: MultiSet, x: Box, y: Box :: { MultiSet#UnionOne(a, x), a[y] }
  //   x != y ==> a[y] == MultiSet#UnionOne(a, x)[y]);
  lemma {:extract_pattern UnionOne(a, x), Multiplicity(a, y)} OtherElementsUnchanged(a: Multiset, x: Box, y: Box)
    requires x != y
    ensures Multiplicity(a, y) == Multiplicity(UnionOne(a, x), y)
  {
    if a.Cons? {
      TailIncreasing(a);
    }
  }

  // axiom (forall a: MultiSet, x: Box :: { MultiSet#Card(MultiSet#UnionOne(a, x)) }
  //   MultiSet#Card(MultiSet#UnionOne(a, x)) == MultiSet#Card(a) + 1);
  lemma {:extract_pattern Card(UnionOne(a, x))} CardUnionOne(a: Multiset, x: Box)
    ensures Card(UnionOne(a, x)) == Card(a) + 1
  {
    if a.Cons? {
      TailIncreasing(a);
    }
  }

  // function MultiSet#Union(MultiSet, MultiSet): MultiSet;
  function {:extract_boogie_name "MultiSet#Union"} Union(a: Multiset, b: Multiset): Multiset {
    match a
    case Nil => b
    case Cons(x, tail) =>
      TailIncreasing(a);
      Union(tail, UnionOne(b, x))
  }

  // // union-ing is the sum of the contents
  // axiom (forall a: MultiSet, b: MultiSet, o: Box :: { MultiSet#Union(a,b)[o] }
  //   MultiSet#Union(a,b)[o] == a[o] + b[o]);
  lemma {:extract_pattern Multiplicity(Union(a, b), o)} MultiplicityUnion(a: Multiset, b: Multiset, o: Box)
    ensures Multiplicity(Union(a, b), o) == Multiplicity(a, o) + Multiplicity(b, o)
  {
    match a
    case Nil =>
    case Cons(x, tail) =>
      TailIncreasing(a);
      calc {
        Multiplicity(Union(a, b), o);
        Multiplicity(Union(tail, UnionOne(b, x)), o);
        { MultiplicityUnion(tail, UnionOne(b, x), o); }
        Multiplicity(tail, o) + Multiplicity(UnionOne(b, x), o);
        { MultiplicityDelta(b, x, o); }
        Multiplicity(tail, o) + BoolInt(x == o) + Multiplicity(b, o);
        Multiplicity(a, o) + Multiplicity(b, o);
      }
  }

  // axiom (forall a: MultiSet, b: MultiSet :: { MultiSet#Card(MultiSet#Union(a,b)) }
  //   MultiSet#Card(MultiSet#Union(a,b)) == MultiSet#Card(a) + MultiSet#Card(b));
  lemma {:extract_pattern Card(Union(a, b))} CardUnion(a: Multiset, b: Multiset)
    ensures Card(Union(a, b)) == Card(a) + Card(b)
  {
    match a
    case Nil =>
    case Cons(x, tail) =>
      calc {
        Card(Union(a, b));
        { TailIncreasing(a); }
        Card(Union(tail, UnionOne(b, x)));
        { CardUnion(tail, UnionOne(b, x)); }
        Card(tail) + Card(UnionOne(b, x));
        { CardUnionOne(b, x); }
        Card(tail) + 1 + Card(b);
        Card(a) + Card(b);
      }
  }

  // function MultiSet#Intersection(MultiSet, MultiSet): MultiSet;
  function {:extract_boogie_name "MultiSet#Intersection"} Intersection(a: Multiset, b: Multiset): Multiset {
    match a
    case Nil => Nil
    case Cons(x, tail) =>
      TailIncreasing(a);
      if b.Contains(x) then
        UnionOne(Intersection(tail, RemoveOne(b, x)), x)
      else
        Intersection(tail, b)
  }

  function RemoveOne(a: Multiset, x: Box): Multiset
    requires a.Contains(x)
    decreases a, 0
  {
    TailIncreasing(a);
    if a.head == x then
      a.tail
    else
      TailIncreasing(a);
      a.HeadTailAt();
      RemoveOnePreservesBelow(a.tail, x, a.head);
      PrependPreservesIncreasingAll(a.head, RemoveOne(a.tail, x));
      Cons(a.head, RemoveOne(a.tail, x))
  }

  lemma RemoveOnePreservesBelow(a: Multiset, x: Box, o: Box)
    requires a.Contains(x)
    requires forall i :: 0 <= i < a.Length() ==> Below(o, a.At(i))
    ensures forall i :: 0 <= i < RemoveOne(a, x).Length() ==> Below(o, RemoveOne(a, x).At(i))
    decreases a
  {
    a.HeadTailAt();
    var a' := RemoveOne(a, x);
    if a.head == x {
      assert a' == a.tail;
    } else {
      TailIncreasing(a);
      assert a' == Cons(a.head, RemoveOne(a.tail, x));
    }
  }

  lemma MultiplicityRemoveOne(a: Multiset, x: Box, o: Box)
    requires a.Contains(x)
    ensures Multiplicity(RemoveOne(a, x), o) == Multiplicity(a, o) - BoolInt(x == o)
  {
    var a' := RemoveOne(a, x);
    if a.head == x {
      assert a' == a.tail;
    } else {
      TailIncreasing(a);
      assert a' == Cons(a.head, RemoveOne(a.tail, x));
    }
  }

  // axiom (forall a: MultiSet, b: MultiSet, o: Box :: { MultiSet#Intersection(a,b)[o] }
  //   MultiSet#Intersection(a,b)[o] == Math#min(a[o],  b[o]));
  lemma {:extract_pattern Multiplicity(Intersection(a, b), o)} MultiplicityIntersection(a: Multiset, b: Multiset, o: Box)
    ensures Multiplicity(Intersection(a, b), o) == Math.Min(Multiplicity(a, o), Multiplicity(b, o))
  {
    var intersection := Intersection(a, b);
    match a
    case Nil =>
      assert intersection == Nil;
      calc {
        Multiplicity(intersection, o);
        0;
        { MultiplicityCard(b, o); Math.Min0(0, Multiplicity(b, o)); }
        Math.Min(0, Multiplicity(b, o));
        Math.Min(Multiplicity(a, o), Multiplicity(b, o));
      }
    case Cons(x, tail) =>
      TailIncreasing(a);
      if b.Contains(x) {
        assert intersection == UnionOne(Intersection(tail, RemoveOne(b, x)), x);
        var intersection' := Intersection(tail, RemoveOne(b, x));
        calc {
          Multiplicity(intersection, o);
          Multiplicity(UnionOne(intersection', x), o);
          { MultiplicityDelta(intersection', x, o); }
          Multiplicity(intersection', o) + BoolInt(x == o);
          { MultiplicityIntersection(tail, RemoveOne(b, x), o); }
          Math.Min(Multiplicity(tail, o), Multiplicity(RemoveOne(b, x), o)) + BoolInt(x == o);
          { MultiplicityRemoveOne(b, x, o); }
          Math.Min(Multiplicity(tail, o), Multiplicity(b, o) - BoolInt(x == o)) + BoolInt(x == o);
          { assert Multiplicity(a, o) == BoolInt(x == o) + Multiplicity(tail, o); }
          Math.Min(Multiplicity(a, o) - BoolInt(x == o), Multiplicity(b, o) - BoolInt(x == o)) + BoolInt(x == o);
          { MinDistribution(Multiplicity(a, o), Multiplicity(b, o), BoolInt(x == o)); }
          Math.Min(Multiplicity(a, o), Multiplicity(b, o));
        }
      } else if x != o {
        // proof automatic
      } else {
        assert intersection == Intersection(tail, b);
        calc {
          Multiplicity(intersection, o);
          Multiplicity(Intersection(tail, b), o);
          { MultiplicityIntersection(tail, b, o); }
          Math.Min(Multiplicity(tail, o), Multiplicity(b, o));
          { ZeroMultiplicityForNonElements(b, o); }
          Math.Min(Multiplicity(tail, o), 0);
          { ZeroMinMultiplicity(tail, o); }
          0;
          { ZeroMinMultiplicity(a, o); }
          Math.Min(Multiplicity(a, o), 0);
          { ZeroMultiplicityForNonElements(b, o); }
          Math.Min(Multiplicity(a, o), Multiplicity(b, o));
        }
      }
  }

  lemma ZeroMinMultiplicity(a: Multiset, o: Box)
    ensures Math.Min(0, Multiplicity(a, o)) == 0 == Math.Min(Multiplicity(a, o), 0)
  {
    var multiplicity := Multiplicity(a, o);
    assert 0 <= multiplicity by {
      MultiplicityCard(a, o);
    }
    assert Math.Min(0, multiplicity) == 0 by {
      Math.Min0(0, multiplicity);
    }
    assert Math.Min(multiplicity, 0) == 0 by {
      Math.Min1(multiplicity, 0);
    }
  }

  // The axioms about Min in module Math have been crafted for extraction into the Dafny prelude.
  // But they speak of a precise definition of Min, which we prove here.
  lemma RevealMin()
    ensures forall a, b :: Math.Min(a, b) == if a < b then a else b
  {
    forall a, b
      ensures Math.Min(a, b) == if a < b then a else b
    {
      if a < b {
        Math.Min0(a, b);
      } else {
        Math.Min1(a, b);
      }
    }
  }

  lemma MinDistribution(a: int, b: int, c: int)
    ensures Math.Min(a - c, b - c) == Math.Min(a, b) - c
  {
    RevealMin();
  }

  // // left and right pseudo-idempotence
  // axiom (forall a, b: MultiSet :: { MultiSet#Intersection(MultiSet#Intersection(a, b), b) }
  //   MultiSet#Intersection(MultiSet#Intersection(a, b), b) == MultiSet#Intersection(a, b));
  lemma {:extract_pattern Intersection(Intersection(a, b), b)} IntersectionPseudoIdempotenceB(a: Multiset, b: Multiset)
    ensures Intersection(Intersection(a, b), b) == Intersection(a, b)
  {
    var ab := Intersection(a, b);
    forall o {
      calc {
        Multiplicity(Intersection(ab, b), o);
        { MultiplicityIntersection(ab, b, o); }
        Math.Min(Multiplicity(ab, o), Multiplicity(b, o));
        { MultiplicityIntersection(a, b, o); }
        Math.Min(Math.Min(Multiplicity(a, o), Multiplicity(b, o)), Multiplicity(b, o));
        { RevealMin(); }
        Math.Min(Multiplicity(a, o), Multiplicity(b, o));
        { MultiplicityIntersection(a, b, o); }
        Multiplicity(Intersection(a, b), o);
      }
    }
    Extensionality(Intersection(ab, b), ab);
  }

  // axiom (forall a, b: MultiSet :: { MultiSet#Intersection(a, MultiSet#Intersection(a, b)) }
  //   MultiSet#Intersection(a, MultiSet#Intersection(a, b)) == MultiSet#Intersection(a, b));
  lemma {:extract_pattern Intersection(a, Intersection(a, b))} IntersectionPseudoIdempotenceA(a: Multiset, b: Multiset)
    ensures Intersection(a, Intersection(a, b)) == Intersection(a, b)
  {
    var ab := Intersection(a, b);
    forall o {
      calc {
        Multiplicity(Intersection(a, ab), o);
        { MultiplicityIntersection(a, ab, o); }
        Math.Min(Multiplicity(a, o), Multiplicity(ab, o));
        { MultiplicityIntersection(a, b, o); }
        Math.Min(Multiplicity(a, o), Math.Min(Multiplicity(a, o), Multiplicity(b, o)));
        { RevealMin(); }
        Math.Min(Multiplicity(a, o), Multiplicity(b, o));
        { MultiplicityIntersection(a, b, o); }
        Multiplicity(Intersection(a, b), o);
      }
    }
    Extensionality(Intersection(a, ab), ab);
  }

  // // multiset difference, a - b. clip() makes it positive.
  // function MultiSet#Difference(MultiSet, MultiSet): MultiSet;
  function {:extract_boogie_name "MultiSet#Difference"} Difference(a: Multiset, b: Multiset): Multiset {
    match a
    case Nil => Nil
    case Cons(x, tail) =>
      TailIncreasing(a);
      if b.Contains(x) then
        Difference(tail, RemoveOne(b, x))
      else
        UnionOne(Difference(tail, b), x)
  }

  lemma ClipNonPos(i: int)
    requires i <= 0
    ensures Math.Clip(i) == 0
  {
    if i == 0 {
      Math.ClipId(i);
    } else {
      Math.ClipZero(i);
    }
  }

  lemma ClipDistribution(a: nat, b: nat)
    ensures Math.Clip(a) + b == Math.Clip(a + b)
  {
    calc {
      Math.Clip(a) + b;
      { Math.ClipId(a); }
      a + b;
      { Math.ClipId(a + b); }
      Math.Clip(a + b);
    }
  }

  // axiom (forall a: MultiSet, b: MultiSet, o: Box :: { MultiSet#Difference(a,b)[o] }
  //   MultiSet#Difference(a,b)[o] == Math#clip(a[o] - b[o]));
  lemma {:extract_pattern Multiplicity(Difference(a, b), o)} MultiplicityDifference(a: Multiset, b: Multiset, o: Box)
    ensures Multiplicity(Difference(a, b), o) == Math.Clip(Multiplicity(a, o) - Multiplicity(b, o))
  {
    var d := Difference(a, b);
    match a
    case Nil =>
      assert d == Nil;
      assert Multiplicity(d, o) == 0 == Multiplicity(a, o);
      MultiplicityCard(b, o);
      ClipNonPos(0 - Multiplicity(b, o));
    case Cons(x, tail) =>
      TailIncreasing(a);
      if b.Contains(x) {
        assert d == Difference(tail, RemoveOne(b, x));
        calc {
          Multiplicity(d, o);
          Multiplicity(Difference(tail, RemoveOne(b, x)), o);
          { MultiplicityDifference(tail, RemoveOne(b, x), o); }
          Math.Clip(Multiplicity(tail, o) - Multiplicity(RemoveOne(b, x), o));
          { MultiplicityRemoveOne(b, x, o); }
          Math.Clip(Multiplicity(tail, o) - Multiplicity(b, o) + BoolInt(x == o));
          { assert Multiplicity(a, o) == BoolInt(x == o) + Multiplicity(tail, o); }
          Math.Clip(Multiplicity(a, o) - Multiplicity(b, o));
        }
      } else {
        assert d == UnionOne(Difference(tail, b), x);
        calc {
          Multiplicity(d, o);
          Multiplicity(UnionOne(Difference(tail, b), x), o);
          { MultiplicityDelta(Difference(tail, b), x, o); }
          Multiplicity(Difference(tail, b), o) + BoolInt(x == o);
          { MultiplicityDifference(tail, b, o); }
          Math.Clip(Multiplicity(tail, o) - Multiplicity(b, o)) + BoolInt(x == o);
        }
        if x == o {
          calc {
            Math.Clip(Multiplicity(tail, o) - Multiplicity(b, o)) + BoolInt(x == o);
            { ZeroMultiplicityForNonElements(b, o); }
            Math.Clip(Multiplicity(tail, o)) + BoolInt(x == o);
            { ClipMultiplicity(tail, o); }
            Multiplicity(tail, o) + BoolInt(x == o);
            Multiplicity(a, o);
            { ClipMultiplicity(a, o); }
            Math.Clip(Multiplicity(a, o));
            { ZeroMultiplicityForNonElements(b, o); }
            Math.Clip(Multiplicity(a, o) - Multiplicity(b, o));
          }
        } else {
          calc {
            Math.Clip(Multiplicity(tail, o) - Multiplicity(b, o)) + BoolInt(x == o);
            Math.Clip(Multiplicity(a, o) - BoolInt(x == o) - Multiplicity(b, o)) + BoolInt(x == o);
            Math.Clip(Multiplicity(a, o) - Multiplicity(b, o));
          }
        }
      }
  }

  lemma ClipMultiplicity(a: Multiset, o: Box)
    ensures Math.Clip(Multiplicity(a, o)) == Multiplicity(a, o)
  {
    var multiplicity := Multiplicity(a, o);
    assert 0 <= multiplicity by {
      MultiplicityCard(a, o);
    }
    Math.ClipId(multiplicity);
  }

  // axiom (forall a, b: MultiSet, y: Box :: { MultiSet#Difference(a, b), b[y], a[y] }
  //   a[y] <= b[y] ==> MultiSet#Difference(a, b)[y] == 0 );
  lemma {:extract_pattern Difference(a, b), Multiplicity(b, y), Multiplicity(a, y)} MultiplicityDifferenceOnDominant(a: Multiset, b: Multiset, y: Box)
    requires Multiplicity(a, y) <= Multiplicity(b, y)
    ensures Multiplicity(Difference(a, b), y) == 0
  {
    calc {
      Multiplicity(Difference(a, b), y);
      { MultiplicityDifference(a, b, y); }
      Math.Clip(Multiplicity(a, y) - Multiplicity(b, y));
      { ClipNonPos(Multiplicity(a, y) - Multiplicity(b, y)); }
      0;
    }
  }

  // axiom (forall a, b: MultiSet ::
  //   { MultiSet#Card(MultiSet#Difference(a, b)) }
  //   MultiSet#Card(MultiSet#Difference(a, b)) + MultiSet#Card(MultiSet#Difference(b, a))
  //   + 2 * MultiSet#Card(MultiSet#Intersection(a, b))
  //     == MultiSet#Card(MultiSet#Union(a, b)) &&
  //   MultiSet#Card(MultiSet#Difference(a, b)) == MultiSet#Card(a) - MultiSet#Card(MultiSet#Intersection(a, b)));
  lemma {:extract_pattern Card(Difference(a, b))} CardDifference(a: Multiset, b: Multiset)
    ensures Card(Difference(a, b)) + Card(Difference(b, a)) + 2 * Card(Intersection(a, b)) == Card(Union(a, b))
    ensures Card(Difference(a, b)) == Card(a) - Card(Intersection(a, b))
  {
    var dab := Difference(a, b);
    var dba := Difference(b, a);
    var iab := Intersection(a, b);
    var uab := Union(a, b);

    assert L0: Union(dab, Union(dba, Union(iab, iab))) == uab by {
      forall o
        ensures Multiplicity(Union(dab, Union(dba, Union(iab, iab))), o) == Multiplicity(uab, o)
      {
        var ma := Multiplicity(a, o);
        var mb := Multiplicity(b, o);
        calc {
          Multiplicity(Union(dab, Union(dba, Union(iab, iab))), o);
          { MultiplicityUnion(dab, Union(dba, Union(iab, iab)), o); }
          Multiplicity(dab, o) + Multiplicity(Union(dba, Union(iab, iab)), o);
          { MultiplicityUnion(dba, Union(iab, iab), o); }
          Multiplicity(dab, o) + Multiplicity(dba, o) + Multiplicity(Union(iab, iab), o);
          { MultiplicityUnion(iab, iab, o); }
          Multiplicity(dab, o) + Multiplicity(dba, o) + 2 * Multiplicity(iab, o);
          { MultiplicityDifference(a, b, o); }
          Math.Clip(ma - mb) + Multiplicity(dba, o) + 2 * Multiplicity(iab, o);
          { MultiplicityDifference(b, a, o); }
          Math.Clip(ma - mb) + Math.Clip(mb - ma) + 2 * Multiplicity(iab, o);
          { MultiplicityIntersection(a, b, o); }
          Math.Clip(ma - mb) + Math.Clip(mb - ma) + 2 * Math.Min(ma, mb);
          {
            if ma <= mb {
              ClipNonPos(ma - mb);
              Math.ClipId(mb - ma);
              Math.Min0(ma, mb);
            } else {
              Math.ClipId(ma - mb);
              Math.ClipZero(mb - ma);
              Math.Min1(ma, mb);
            }
          }
          ma + mb;
          { MultiplicityUnion(a, b, o); }
          Multiplicity(uab, o);
        }
      }
      Extensionality(Union(dab, Union(dba, Union(iab, iab))), uab);
    }

    assert L1: Union(dab, iab) == a by {
      forall o {
        calc {
          Multiplicity(Union(dab, iab), o);
          { MultiplicityUnion(dab, iab, o); }
          Multiplicity(dab, o) + Multiplicity(iab, o);
          { MultiplicityDifference(a, b, o); }
          Math.Clip(Multiplicity(a, o) - Multiplicity(b, o)) + Multiplicity(iab, o);
          { MultiplicityIntersection(a, b, o); }
          Math.Clip(Multiplicity(a, o) - Multiplicity(b, o)) + Math.Min(Multiplicity(a, o), Multiplicity(b, o));
          {
            var ma := Multiplicity(a, o);
            var mb := Multiplicity(b, o);
            if mb <= ma {
              Math.ClipId(ma - mb);
              Math.Min1(ma, mb);
            } else {
              Math.ClipZero(ma - mb);
              Math.Min0(ma, mb);
            }
          }
          Multiplicity(a, o);
        }
      }
      Extensionality(Union(dab,iab), a);
    }

    calc {
      Card(uab);
      { reveal L0; }
      Card(Union(dab, Union(dba, Union(iab, iab))));
      { CardUnion(dab, Union(dba, Union(iab, iab))); }
      Card(dab) + Card(Union(dba, Union(iab, iab)));
      { CardUnion(dba, Union(iab, iab)); }
      Card(dab) + Card(dba) + Card(Union(iab, iab));
      { CardUnion(iab, iab); }
      Card(dab) + Card(dba) + 2 * Card(iab);
    }

    calc {
      Card(a);
      { reveal L1; }
      Card(Union(dab, iab));
      { CardUnion(dab, iab); }
      Card(dab) + Card(iab);
    }
  }

  // // multiset subset means a must have at most as many of each element as b
  // function MultiSet#Subset(MultiSet, MultiSet): bool;
  ghost predicate {:extract_boogie_name "MultiSet#Subset"} Subset(a: Multiset, b: Multiset) {
    forall o :: Multiplicity(a, o) <= Multiplicity(b, o)
  }

  // axiom (forall a: MultiSet, b: MultiSet :: { MultiSet#Subset(a,b) }
  //   MultiSet#Subset(a,b) <==> (forall o: Box :: {a[o]} {b[o]} a[o] <= b[o]));
  lemma {:extract_pattern Subset(a, b)} SubsetDefinition(a: Multiset, b: Multiset)
    ensures Subset(a, b) <==> forall o {:extract_pattern Multiplicity(a, o)} {:extract_pattern Multiplicity(b, o)} :: Multiplicity(a, o) <= Multiplicity(b, o)
  {
    if !Subset(a, b) {
      var o := ExhibitSubsetDifference(a, b);
    }
  }

  lemma ExhibitSubsetDifference(a: Multiset, b: Multiset) returns (o: Box)
    requires !Subset(a, b)
    ensures Multiplicity(a, o) > Multiplicity(b, o)
  {
    if a == Nil {
      assert Subset(a, b) by {
        forall o {
          calc {
            Multiplicity(a, o);
            0;
          <=  { MultiplicityCard(b, o); }
            Multiplicity(b, o);
          }
        }
      }
      assert false;
    } else if b == Nil {
      o := a.head;
      assert Multiplicity(b, o) == 0;
      assert Multiplicity(a, o) > 0 by {
        TailIncreasing(a);
        MultiplicityCard(a.tail, o);
      }
    } else if a.head == b.head {
      var x := a.head;
      TailIncreasing(a);
      TailIncreasing(b);
      assert !Subset(a.tail, b.tail) by {
        if Subset(a.tail, b.tail) {
          assert Subset(a, b);
          assert false;
        }
      }
      o := ExhibitSubsetDifference(a.tail, b.tail);
    } else if Less(a.head, b.head) {
      o := a.head;
      assert Multiplicity(a, o) > 0 by {
        TailIncreasing(a);
        MultiplicityCard(a.tail, o);
      }
      assert Multiplicity(b, o) == 0 by {
        ZeroMultiplicityForLargerElements(b, o);
      }
    } else {
      assert Less(b.head, a.head) by {
        Connected(a.head, b.head);
      }
      TailIncreasing(a);
      TailIncreasing(b);
      o := ExhibitSubsetDifference(a, b.tail);
      assert IH: Multiplicity(a, o) > Multiplicity(b.tail, o);
      assert Multiplicity(b, o) == Multiplicity(b.tail, o) by {
        assert Multiplicity(b, o) == BoolInt(b.head == o) + Multiplicity(b.tail, o);
        assert b.head != o by {
          if b.head == o {
            // Because Less(b.head, a.head), the condition "b.head == o" would mean
            // Multiplicity(a, o) == 0. But we have Multiplicity(a, o) > 0 from the IH.
            assert Multiplicity(a, o) > 0 by {
              reveal IH;
              MultiplicityCard(b.tail, o);
            }
            assert Multiplicity(a, o) == 0 by {
              ZeroMultiplicityForLargerElements(a, o);
            }
            assert false;
          }
        }
      }
    }
  }

  // function MultiSet#Equal(MultiSet, MultiSet): bool;
  ghost predicate {:extract_boogie_name "MultiSet#Equal"} Equal(a: Multiset, b: Multiset) {
    forall o :: Multiplicity(a, o) == Multiplicity(b, o)
  }

  // axiom (forall a: MultiSet, b: MultiSet :: { MultiSet#Equal(a,b) }
  //   MultiSet#Equal(a,b) <==> (forall o: Box :: {a[o]} {b[o]} a[o] == b[o]));
  lemma {:extract_pattern Equal(a, b)} EqualDefinition(a: Multiset, b: Multiset)
    ensures Equal(a, b) <==>
            forall o {:extract_pattern Multiplicity(a, o)} {:extract_pattern Multiplicity(b, o)} ::
              Multiplicity(a, o) == Multiplicity(b, o)
  {
    if a != b {
      var o := ExhibitDifference(a, b);
    }
  }

  lemma ExhibitDifference(a: Multiset, b: Multiset) returns (o: Box)
    requires a != b
    ensures Multiplicity(a, o) != Multiplicity(b, o)
    decreases a != Nil, a.Cons? && b.Cons? && !Less(a.head, b.head), a
  {
    if a == Nil {
      o := b.head;
      assert Multiplicity(a, o) == 0;
      assert Multiplicity(b, o) > 0 by {
        TailIncreasing(b);
        MultiplicityCard(b.tail, o);
      }
    } else if b == Nil {
      o := ExhibitDifference(b, a);
    } else if a.head == b.head {
      TailIncreasing(a);
      TailIncreasing(b);
      o := ExhibitDifference(a.tail, b.tail);
    } else if Less(a.head, b.head) {
      o := a.head;
      assert Multiplicity(a, o) > 0 by {
        TailIncreasing(a);
        MultiplicityCard(a.tail, o);
      }
      assert Multiplicity(b, o) == 0 by {
        ZeroMultiplicityForLargerElements(b, o);
      }
    } else {
      assert Less(b.head, a.head) by {
        Connected(a.head, b.head);
      }
      o := ExhibitDifference(b, a);
    }
  }

  // // extensionality axiom for multisets
  // axiom (forall a: MultiSet, b: MultiSet :: { MultiSet#Equal(a,b) }
  //   MultiSet#Equal(a,b) ==> a == b);
  lemma {:extract_pattern Equal(a, b)} Extensionality(a: Multiset, b: Multiset)
    requires Equal(a, b)
    ensures a == b
  {
    if a != b {
      var o := ExhibitDifference(a, b);
      assert false;
    }
  }

  // function MultiSet#Disjoint(MultiSet, MultiSet): bool;
  ghost predicate {:extract_boogie_name "MultiSet#Disjoint"} Disjoint(a: Multiset, b: Multiset) {
    forall o :: Multiplicity(a, o) == 0 || Multiplicity(b, o) == 0
  }

  // Because of the fuel parameter getting in the way of quantifier matching patterns, DisjointDefinition is not
  // straightforward for the verifier. As a workaround, we introduce another function, MultiplicityWrapper, that is
  // used as a trigger for the quantifier in DisjointDefinition. (Once Dafny's encoding changes to move the fuel
  // parameter to the CanCall, then this workaround will no longer be needed.)
  function MultiplicityWrapper(a: Multiset, o: Box): int {
    Multiplicity(a, o)
  }

  // axiom (forall a: MultiSet, b: MultiSet :: { MultiSet#Disjoint(a,b) }
  //   MultiSet#Disjoint(a,b) <==> (forall o: Box :: {a[o]} {b[o]} a[o] == 0 || b[o] == 0));
  lemma {:extract_pattern Disjoint(a, b)} DisjointDefinition(a: Multiset, b: Multiset)
    ensures Disjoint(a, b) <==>
            forall o {:extract_pattern Multiplicity(a, o)} {:extract_pattern Multiplicity(b, o)} {:trigger MultiplicityWrapper(a, o)} ::
              Multiplicity(a, o) == 0 || Multiplicity(b, o) == 0
  {
    if !Disjoint(a, b) {
      var o :| Multiplicity(a, o) != 0 && Multiplicity(b, o) != 0;
      assert MultiplicityWrapper(a, o) == Multiplicity(a, o);
    }
  }

  // // conversion to a multiset. each element in the original set has duplicity 1.
  // function MultiSet#FromSet(Set): MultiSet;
  function {:extract_boogie_name "MultiSet#FromSet"} FromSet(s: Sets.Set): Multiset {
    s
  }

  lemma MultiplicityFromSetIsBinary(s: Sets.Set, o: Box)
    ensures 0 <= Multiplicity(FromSet(s), o) <= 1
  {
    match s
    case Nil =>
    case Cons(x, tail) =>
      Sets.TailStrictlyIncreasing(s);
      assert Multiplicity(s, o) == BoolInt(x == o) + Multiplicity(tail, o);
      if x == o {
        assert !tail.Contains(o) by {
          if tail.Contains(o) {
            var i := tail.ContainsAt(o);
            assert o == tail.At(i) == s.At(i + 1);
            assert x == s.At(0);
            assert Less(s.At(0), s.At(i + 1));
            assert x != o;
            assert false;
          }
        }
        NonZeroMultiplicityForElements(tail, o);
      } else {
        MultiplicityFromSetIsBinary(tail, o);
      }
  }

  // axiom (forall s: Set, a: Box :: { MultiSet#FromSet(s)[a] }
  //   (MultiSet#FromSet(s)[a] == 0 <==> !s[a]) &&
  //   (MultiSet#FromSet(s)[a] == 1 <==> s[a]));
  lemma {:extract_pattern Multiplicity(FromSet(s), a)} MultiplicityFromSet(s: Sets.Set, a: Box)
    ensures Multiplicity(FromSet(s), a) == 0 <==> !Sets.IsMember(s, a)
    ensures Multiplicity(FromSet(s), a) == 1 <==> Sets.IsMember(s, a)
  {
    calc {
      Multiplicity(FromSet(s), a) == 0;
      Multiplicity(s, a) == 0;
      { NonZeroMultiplicityForElements(s, a); }
      !s.Contains(a);
      !Sets.IsMember(s, a);
    }

    MultiplicityFromSetIsBinary(s, a);
  }

  // axiom (forall s: Set :: { MultiSet#Card(MultiSet#FromSet(s)) }
  //   MultiSet#Card(MultiSet#FromSet(s)) == Set#Card(s));
  lemma {:extract_pattern Card(FromSet(s))} CardFromSet(s: Sets.Set)
    ensures Card(FromSet(s)) == Sets.Card(s)
  {
  }

  // // conversion to a multiset, from a sequence.
  // function MultiSet#FromSeq(Seq): MultiSet uses {
  //   axiom MultiSet#FromSeq(Seq#Empty(): Seq) == MultiSet#Empty(): MultiSet;
  // }
  function {:extract_boogie_name "MultiSet#FromSeq"} FromSeq(s: Sequences.Seq): Multiset {
    match s
    case Nil => Nil
    case Cons(x, tail) =>
      UnionOne(FromSeq(tail), x)
  }

  lemma {:extract_used_by FromSeq} FromEmptySeq()
    ensures FromSeq(Sequences.Empty()) == Empty()
  {
  }

  // // conversion produces a good map.
  // axiom (forall s: Seq :: { MultiSet#FromSeq(s) } $IsGoodMultiSet(MultiSet#FromSeq(s)) );
  lemma {:extract_pattern FromSeq(s)} ConversionGivesGoodMultiset(s: Sequences.Seq)
    ensures IsGood(FromSeq(s))
  {
  }

  // // cardinality axiom
  // axiom (forall s: Seq ::
  //   { MultiSet#Card(MultiSet#FromSeq(s)) }
  //     MultiSet#Card(MultiSet#FromSeq(s)) == Seq#Length(s));
  lemma {:extract_pattern Card(FromSeq(s))} CardFromSeq(s: Sequences.Seq)
    ensures Card(FromSeq(s)) == Sequences.Length(s)
  {
    match s
    case Nil =>
    case Cons(x, tail) =>
      calc {
        Card(FromSeq(s));
        Card(UnionOne(FromSeq(tail), x));
        { CardUnionOne(FromSeq(tail), x); }
        1 + Card(FromSeq(tail));
        { CardFromSeq(tail); }
        1 + Sequences.Length(tail);
        Sequences.Length(s);
      }
  }

  // // building axiom
  // axiom (forall s: Seq, v: Box ::
  //   { MultiSet#FromSeq(Seq#Build(s, v)) }
  //     MultiSet#FromSeq(Seq#Build(s, v)) == MultiSet#UnionOne(MultiSet#FromSeq(s), v)
  //   );
  lemma {:extract_pattern FromSeq(Sequences.Build(s, v))} BuildFromSeq(s: Sequences.Seq, v: Box)
    ensures FromSeq(Sequences.Build(s, v)) == UnionOne(FromSeq(s), v)
  {
    var ss, vv := FromSeq(s), Cons(v, Nil);
    calc {
      FromSeq(Sequences.Build(s, v));
      FromSeq(s.Append(Cons(v, Nil)));
      FromSeq(Sequences.Append(s, Cons(v, Nil)));
      { Concatenation(s, Cons(v, Nil)); }
      Union(ss, FromSeq(Cons(v, Nil)));
      Union(ss, UnionOne(FromSeq(Nil), v));
      Union(ss, UnionOne(Nil, v));
      Union(ss, vv);
    }

    forall o {
      calc {
        Multiplicity(FromSeq(Sequences.Build(s, v)), o);
        Multiplicity(Union(ss, vv), o);
        { MultiplicityUnion(ss, vv, o); }
        Multiplicity(ss, o) + Multiplicity(vv, o);
        Multiplicity(ss, o) + BoolInt(v == o);
        { MultiplicityDelta(ss, v, o); }
        Multiplicity(UnionOne(ss, v), o);
      }
    }
    Extensionality(FromSeq(Sequences.Build(s, v)), UnionOne(ss, v));
  }

  // // concatenation axiom
  // axiom (forall a: Seq, b: Seq ::
  //   { MultiSet#FromSeq(Seq#Append(a, b)) }
  //     MultiSet#FromSeq(Seq#Append(a, b)) == MultiSet#Union(MultiSet#FromSeq(a), MultiSet#FromSeq(b)) );
  lemma {:extract_pattern FromSeq(Sequences.Append(a, b))} Concatenation(a: Sequences.Seq, b: Sequences.Seq)
    ensures FromSeq(Sequences.Append(a, b)) == Union(FromSeq(a), FromSeq(b))
  {
    forall o {
      calc {
        Multiplicity(FromSeq(Sequences.Append(a, b)), o);
        { MultiplicityFromSeqAppend(a, b, o); }
        Multiplicity(FromSeq(a), o) + Multiplicity(FromSeq(b), o);
        { MultiplicityUnion(FromSeq(a), FromSeq(b), o); }
        Multiplicity(Union(FromSeq(a), FromSeq(b)), o);
      }
    }
    Extensionality(FromSeq(Sequences.Append(a, b)), Union(FromSeq(a), FromSeq(b)));
  }

  lemma MultiplicityFromSeqAppend(a: Sequences.Seq, b: Sequences.Seq, o: Box)
    ensures Multiplicity(FromSeq(Sequences.Append(a, b)), o) == Multiplicity(FromSeq(a), o) + Multiplicity(FromSeq(b), o)
  {
    match a
    case Nil =>
    case Cons(x, tail) =>
      calc {
        Multiplicity(FromSeq(Sequences.Append(a, b)), o);
        Multiplicity(FromSeq(Cons(x, Sequences.Append(tail, b))), o);
        Multiplicity(UnionOne(FromSeq(Sequences.Append(tail, b)), x), o);
        { MultiplicityDelta(FromSeq(Sequences.Append(tail, b)), x, o); }
        Multiplicity(FromSeq(Sequences.Append(tail, b)), o) + BoolInt(x == o);
        { MultiplicityFromSeqAppend(tail, b, o); }
        Multiplicity(FromSeq(tail), o) + Multiplicity(FromSeq(b), o) + BoolInt(x == o);
        { MultiplicityDelta(FromSeq(tail), x, o); }
        Multiplicity(UnionOne(FromSeq(tail), x), o) + Multiplicity(FromSeq(b), o);
        Multiplicity(FromSeq(a), o) + Multiplicity(FromSeq(b), o);
      }
  }

  // // update axiom
  // axiom (forall s: Seq, i: int, v: Box, x: Box ::
  //   { MultiSet#FromSeq(Seq#Update(s, i, v))[x] }
  //     0 <= i && i < Seq#Length(s) ==>
  //     MultiSet#FromSeq(Seq#Update(s, i, v))[x] ==
  //       MultiSet#Union(MultiSet#Difference(MultiSet#FromSeq(s), MultiSet#Singleton(Seq#Index(s,i))), MultiSet#Singleton(v))[x] );
  //   // i.e. MS(Update(s, i, v)) == MS(s) - {{s[i]}} + {{v}}
  lemma {:extract_pattern Multiplicity(FromSeq(Sequences.Update(s, i, v)), x)} AboutUpdate(s: Sequences.Seq, i: int, v: Box, x: Box)
    requires 0 <= i < Sequences.Length(s)
    ensures
      Multiplicity(FromSeq(Sequences.Update(s, i, v)), x) ==
      Multiplicity(Union(Difference(FromSeq(s), Singleton(Sequences.Index(s, i))), Singleton(v)), x)
  {
    assert s.Cons?; // since Sequences.Length(s) != 0

    var ss, vv := FromSeq(s), Cons(v, Nil);
    var y, tail := s.head, s.tail;

    if i == 0 {
      assert Sequences.Index(s, i) == y;
      var yy := Singleton(y);

      calc {
        Multiplicity(FromSeq(Sequences.Update(s, i, v)), x);
        Multiplicity(FromSeq(Cons(v, tail)), x);
        { assert Cons(v, tail) == Cons(v, Sequences.Append(Nil, tail)) == Sequences.Append(vv, tail); }
        Multiplicity(FromSeq(Sequences.Append(vv, tail)), x);
        { MultiplicityFromSeqAppend(vv, tail, x); }
        Multiplicity(FromSeq(vv), x) + Multiplicity(FromSeq(tail), x);
        { assert FromSeq(vv) == vv; }
        Multiplicity(vv, x) + Multiplicity(FromSeq(tail), x);
        { ClipMultiplicity(FromSeq(tail), x); }
        Multiplicity(vv, x) + Math.Clip(Multiplicity(FromSeq(tail), x));
        { MultiplicityFromSeqCons(s, x); }
        Multiplicity(vv, x) + Math.Clip(Multiplicity(ss, x) - BoolInt(y == x));
        { assert Multiplicity(yy, x) == BoolInt(y == x); }
        Multiplicity(vv, x) + Math.Clip(Multiplicity(ss, x) - Multiplicity(yy, x));
        { MultiplicityDifference(ss, yy, x); }
        Multiplicity(vv, x) + Multiplicity(Difference(ss, yy), x);
        { MultiplicityUnion(Difference(ss, yy), vv, x); }
        Multiplicity(Union(Difference(ss, yy), vv), x);
        { assert vv == Singleton(v) && y == Sequences.Index(s, i) && yy == Singleton(y); }
        Multiplicity(Union(Difference(ss, Singleton(Sequences.Index(s, i))), Singleton(v)), x);
      }

    } else {
      var uu := Sequences.Update(tail, i - 1, v);
      var si := Sequences.Index(s, i);
      var msix := Multiplicity(Singleton(si), x);
      calc {
        Multiplicity(FromSeq(Sequences.Update(s, i, v)), x);
        Multiplicity(FromSeq(Cons(y, uu)), x);
        Multiplicity(UnionOne(FromSeq(uu), y), x);
        { MultiplicityDelta(FromSeq(uu), y, x); }
        Multiplicity(FromSeq(uu), x) + BoolInt(y == x);
        { AboutUpdate(tail, i - 1, v, x); }
        Multiplicity(Union(Difference(FromSeq(tail), Singleton(Sequences.Index(tail, i - 1))), Singleton(v)), x) + BoolInt(y == x);
        { assert Sequences.Index(tail, i - 1) == Sequences.Index(s, i) == si && vv == Singleton(v); }
        Multiplicity(Union(Difference(FromSeq(tail), Singleton(si)), vv), x) + BoolInt(y == x);
        { MultiplicityUnion(Difference(FromSeq(tail), Singleton(si)), vv, x); }
        Multiplicity(Difference(FromSeq(tail), Singleton(si)), x) + Multiplicity(vv, x) + BoolInt(y == x);
        { MultiplicityDifference(FromSeq(tail), Singleton(si), x); }
        Math.Clip(Multiplicity(FromSeq(tail), x) - msix) + Multiplicity(vv, x) + BoolInt(y == x);
        { assert msix <= Multiplicity(FromSeq(tail), x) by {
            assert Sequences.Index(tail, i - 1) == si;
            tail.AtContains(i - 1, si);
            MultiplicityFromSeqContainment(tail, si, x);
          }
          ClipDistribution(Multiplicity(FromSeq(tail), x) - msix, BoolInt(y == x));
        }
        Math.Clip(Multiplicity(FromSeq(tail), x) + BoolInt(y == x) - msix) + Multiplicity(vv, x);
        { MultiplicityFromSeqCons(s, x); }
        Math.Clip(Multiplicity(FromSeq(s), x) - msix) + Multiplicity(vv, x);
        { MultiplicityDifference(FromSeq(s), Singleton(si), x); }
        Multiplicity(Difference(FromSeq(s), Singleton(si)), x) + Multiplicity(vv, x);
        { MultiplicityUnion(Difference(FromSeq(s), Singleton(si)), vv, x); }
        Multiplicity(Union(Difference(FromSeq(s), Singleton(si)), vv), x);
        Multiplicity(Union(Difference(FromSeq(s), Singleton(Sequences.Index(s, i))), Singleton(v)), x);
      }
    }
  }

  lemma MultiplicityFromSeqContainment(s: Sequences.Seq, v: Box, x: Box)
    requires s.Contains(v)
    ensures Multiplicity(Singleton(v), x) <= Multiplicity(FromSeq(s), x)
  {
    calc {
      Multiplicity(FromSeq(s), x);
      Multiplicity(UnionOne(FromSeq(s.tail), s.head), x);
      { MultiplicityDelta(FromSeq(s.tail), s.head, x); }
      Multiplicity(FromSeq(s.tail), x) + BoolInt(s.head == x);
    }

    if v == s.head {
      calc {
        Multiplicity(FromSeq(s.tail), x) + BoolInt(v == x);
      >=  { MultiplicityCard(FromSeq(s.tail), x); }
        BoolInt(v == x);
          { MultiplicityDelta(Nil, v, x); }
        Multiplicity(UnionOne(Nil, v), x);
      }
    } else {
      assert s.tail.Contains(v);
      calc {
        Multiplicity(FromSeq(s.tail), x) + BoolInt(s.head == x);
      >=
        Multiplicity(FromSeq(s.tail), x);
      >=  { MultiplicityFromSeqContainment(s.tail, v, x); }
        Multiplicity(Singleton(v), x);
      }
    }
  }

  lemma MultiplicityFromSeqCons(s: Sequences.Seq, x: Box)
    requires s.Cons?
    ensures Multiplicity(FromSeq(s), x) == Multiplicity(FromSeq(s.tail), x) + BoolInt(s.head == x)
  {
    calc {
      Multiplicity(FromSeq(s), x);
      Multiplicity(UnionOne(FromSeq(s.tail), s.head), x);
      { MultiplicityDelta(FromSeq(s.tail), s.head, x); }
      Multiplicity(FromSeq(s.tail), x) + BoolInt(s.head == x);
    }
  }

  // axiom (forall s: Seq, x: Box :: { MultiSet#FromSeq(s)[x] }
  //   (exists i : int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && x == Seq#Index(s,i)) <==> 0 < MultiSet#FromSeq(s)[x] );
  lemma {:extract_pattern Multiplicity(FromSeq(s), x)} MultiplicityFromSeq(s: Sequences.Seq, x: Box)
    ensures (exists i {:extract_pattern Sequences.Index(s, i)} :: 0 <= i < Sequences.Length(s) && x == Sequences.Index(s, i))
       <==> 0 < Multiplicity(FromSeq(s), x)
  {
    calc {
      exists i :: 0 <= i < Sequences.Length(s) && x == Sequences.Index(s, i);
      { Sequences.SeqContainsItsElements(s, x); }
      Sequences.Contains(s, x);
      { SequenceAndMultisetContainment(s, x); }
      FromSeq(s).Contains(x);
      {  NonZeroMultiplicityForElements(FromSeq(s), x); }
      Multiplicity(FromSeq(s), x) != 0;
      { MultiplicityCard(FromSeq(s), x); }
      0 < Multiplicity(FromSeq(s), x);
    }
  }

  lemma SequenceAndMultisetContainment(s: Sequences.Seq, o: Box)
    ensures Sequences.Contains(s, o) <==> FromSeq(s).Contains(o)
  {
    match s
    case Nil =>
      calc {
        FromSeq(s).Contains(o);
        Nil.Contains(o);
        false;
        { Sequences.SeqContainsItsElements(s, o); }
        Sequences.Contains(s, o);
      }
    case Cons(x, tail) =>
      calc {
        FromSeq(s).Contains(o);
        UnionOne(FromSeq(tail), x).Contains(o);
        { UnionOneContains(FromSeq(tail), x, o); }
        x == o || FromSeq(tail).Contains(o);
        { SequenceAndMultisetContainment(tail, o); }
        x == o || Sequences.Contains(tail, o);
        { Sequences.TailContains(s, o); }
        Sequences.Contains(s, o);
      }
  }
}
