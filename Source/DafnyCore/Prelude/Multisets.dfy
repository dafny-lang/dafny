module Multisets {
  import opened Boxes
  import opened Lists
  import Math
  import Sets
  import Sequences

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

  function Multiplicity(m: Multiset, o: Box): int

  function UpdateMultiplicity(m: Multiset, o: Box, n: int): Multiset
  // TODO: if n is negagive, just return m

  // function $IsGoodMultiSet(ms: MultiSet): bool;
  predicate {:extract_boogie_name "$IsGoodMultiSet"} IsGood(m: Multiset)
  
  // // ints are non-negative, used after havocing, and for conversion from sequences to multisets.
  // axiom (forall ms: MultiSet :: { $IsGoodMultiSet(ms) }
  //   $IsGoodMultiSet(ms) <==>
  //   (forall bx: Box :: { ms[bx] } 0 <= ms[bx] && ms[bx] <= MultiSet#Card(ms)));
  lemma {:extract_pattern IsGood(ms)} GoodDefinition(ms: Multiset)
    ensures IsGood(ms) <==> forall bx {:extract_pattern Multiplicity(ms, bx)} :: 0 <= Multiplicity(ms, bx) && Multiplicity(ms, bx) <= Card(ms)

  // function MultiSet#Card(MultiSet): int;
  function {:extract_boogie_name "MultiSet#Card"} Card(m: Multiset): int

  // axiom (forall s: MultiSet :: { MultiSet#Card(s) } 0 <= MultiSet#Card(s));
  lemma {:extract_pattern Card(s)} AboutCard(s: Multiset)
    ensures 0 <= Card(s)

  // axiom (forall s: MultiSet, x: Box, n: int :: { MultiSet#Card(s[x := n]) }
  //   0 <= n ==> MultiSet#Card(s[x := n]) == MultiSet#Card(s) - s[x] + n);
  lemma {:extract_pattern Card(UpdateMultiplicity(s, x, n))} CareUpdate(s: Multiset, x: Box, n: int)
    requires 0 <= n
    ensures Card(UpdateMultiplicity(s, x, n)) == Card(s) - Multiplicity(s, x) + n

  // function MultiSet#Empty(): MultiSet;
  function {:extract_boogie_name "MultiSet#Empty"} Empty(): Multiset

  // axiom (forall o: Box :: { MultiSet#Empty()[o] } MultiSet#Empty()[o] == 0);
  lemma {:extract_pattern Multiplicity(Empty(), o)} EmptyMultiplicities(o: Box)
    ensures Multiplicity(Empty(), o) == 0

  // axiom (forall s: MultiSet :: { MultiSet#Card(s) }
  //   (MultiSet#Card(s) == 0 <==> s == MultiSet#Empty()) &&
  //   (MultiSet#Card(s) != 0 ==> (exists x: Box :: 0 < s[x])));
  lemma {:extract_pattern Card(s)} CardVsEmpty(s: Multiset)
    ensures Card(s) == 0 <==> s == Empty()
    ensures Card(s) != 0 ==> exists x :: 0 < Multiplicity(s, x)

  // function MultiSet#Singleton(Box): MultiSet;
  function {:extract_boogie_name "MultiSet#Singleton"} Singleton(o: Box): Multiset {
    var empty := Cons(o, Nil);
    assert empty.Length() == 1;
    empty
  }

  // axiom (forall r: Box, o: Box :: { MultiSet#Singleton(r)[o] } (MultiSet#Singleton(r)[o] == 1 <==> r == o) &&
  //                                                             (MultiSet#Singleton(r)[o] == 0 <==> r != o));
  lemma {:extract_pattern Multiplicity(Singleton(r), o)} AboutSingleton(r: Box, o: Box)
    ensures Multiplicity(Singleton(r), o) == 1 <==> r == o
    ensures Multiplicity(Singleton(r), o) == 0 <==> r != o

  // axiom (forall r: Box :: { MultiSet#Singleton(r) } MultiSet#Singleton(r) == MultiSet#UnionOne(MultiSet#Empty(), r));
  lemma {:extract_pattern Singleton(r)} SingletonUnionOne(r: Box)
    ensures Singleton(r) == UnionOne(Empty(), r)

  // function MultiSet#UnionOne(MultiSet, Box): MultiSet;
  function {:extract_boogie_name "MultiSet#UnionOne"} UnionOne(m: Multiset, o: Box): Multiset

  // // pure containment axiom (in the original multiset or is the added element)
  // axiom (forall a: MultiSet, x: Box, o: Box :: { MultiSet#UnionOne(a,x)[o] }
  //   0 < MultiSet#UnionOne(a,x)[o] <==> o == x || 0 < a[o]);
  lemma {:extract_pattern Multiplicity(UnionOne(a, x), o)} PureContainment(a: Multiset, x: Box, o: Box)
    ensures 0 < Multiplicity(UnionOne(a, x), o) <==> o == x || 0 < Multiplicity(a, o)

  // // union-ing increases count by one
  // axiom (forall a: MultiSet, x: Box :: { MultiSet#UnionOne(a, x) }
  //   MultiSet#UnionOne(a, x)[x] == a[x] + 1);
  lemma {:extract_pattern UnionOne(a, x)} MultiplicityUnionOne(a: Multiset, x: Box)
    ensures Multiplicity(UnionOne(a, x), x) == Multiplicity(a, x) + 1

  // // non-decreasing
  // axiom (forall a: MultiSet, x: Box, y: Box :: { MultiSet#UnionOne(a, x), a[y] }
  //   0 < a[y] ==> 0 < MultiSet#UnionOne(a, x)[y]);
  lemma {:extract_pattern UnionOne(a, x), Multiplicity(a, y)} NonDecreasing(a: Multiset, x: Box, y: Box)
    requires 0 < Multiplicity(a, y)
    ensures 0 < Multiplicity(UnionOne(a, x), y)

  // // other elements unchanged
  // axiom (forall a: MultiSet, x: Box, y: Box :: { MultiSet#UnionOne(a, x), a[y] }
  //   x != y ==> a[y] == MultiSet#UnionOne(a, x)[y]);
  lemma {:extract_pattern UnionOne(a, x), Multiplicity(a, y)} OtherElementsUnchanged(a: Multiset, x: Box, y: Box)
    requires x != y
    ensures Multiplicity(a, y) == Multiplicity(UnionOne(a, x), y)

  // axiom (forall a: MultiSet, x: Box :: { MultiSet#Card(MultiSet#UnionOne(a, x)) }
  //   MultiSet#Card(MultiSet#UnionOne(a, x)) == MultiSet#Card(a) + 1);
  lemma {:Card(UnionOne(a, x))} CardUnionOne(a: Multiset, x: Box)
    ensures Card(UnionOne(a, x)) == Card(a) + 1

  // function MultiSet#Union(MultiSet, MultiSet): MultiSet;
  function {:extract_boogie_name "MultiSet#Union"} Union(a: Multiset, b: Multiset): Multiset

  // // union-ing is the sum of the contents
  // axiom (forall a: MultiSet, b: MultiSet, o: Box :: { MultiSet#Union(a,b)[o] }
  //   MultiSet#Union(a,b)[o] == a[o] + b[o]);
  lemma {:extract_pattern Multiplicity(Union(a, b), o)} MultiplicityUnion(a: Multiset, b: Multiset, o: Box)
    ensures Multiplicity(Union(a, b), o) == Multiplicity(a, o) + Multiplicity(b, o)

  // axiom (forall a: MultiSet, b: MultiSet :: { MultiSet#Card(MultiSet#Union(a,b)) }
  //   MultiSet#Card(MultiSet#Union(a,b)) == MultiSet#Card(a) + MultiSet#Card(b));
  lemma {:extract_pattern Card(Union(a, b))} CardUnion(a: Multiset, b: Multiset)
    ensures Card(Union(a, b)) == Card(a) + Card(b)

  // function MultiSet#Intersection(MultiSet, MultiSet): MultiSet;
  function {:extract_boogie_name "MultiSet#Intersection"} Intersection(a: Multiset, b: Multiset): Multiset

  // axiom (forall a: MultiSet, b: MultiSet, o: Box :: { MultiSet#Intersection(a,b)[o] }
  //   MultiSet#Intersection(a,b)[o] == Math#min(a[o],  b[o]));
  lemma {:extract_pattern Multiplicity(Intersection(a, b), o)} MultiplicityIntersection(a: Multiset, b: Multiset, o: Box)
    ensures Multiplicity(Intersection(a, b), o) == Math.Min(Multiplicity(a, o), Multiplicity(b, o))

  // // left and right pseudo-idempotence
  // axiom (forall a, b: MultiSet :: { MultiSet#Intersection(MultiSet#Intersection(a, b), b) }
  //   MultiSet#Intersection(MultiSet#Intersection(a, b), b) == MultiSet#Intersection(a, b));
  lemma {:extract_pattern Intersection(Intersection(a, b), b)} IntersectionPseudoIdempotenceB(a: Multiset, b: Multiset)
    ensures Intersection(Intersection(a, b), b) == Intersection(a, b)

  // axiom (forall a, b: MultiSet :: { MultiSet#Intersection(a, MultiSet#Intersection(a, b)) }
  //   MultiSet#Intersection(a, MultiSet#Intersection(a, b)) == MultiSet#Intersection(a, b));
  lemma {:extract_pattern Intersection(a, Intersection(a, b))} IntersectionPseudoIdempotenceA(a: Multiset, b: Multiset)
    ensures Intersection(a, Intersection(a, b)) == Intersection(a, b)

  // // multiset difference, a - b. clip() makes it positive.
  // function MultiSet#Difference(MultiSet, MultiSet): MultiSet;
  function {:extract_boogie_name "MultiSet#Difference"} Difference(a: Multiset, b: Multiset): Multiset

  // axiom (forall a: MultiSet, b: MultiSet, o: Box :: { MultiSet#Difference(a,b)[o] }
  //   MultiSet#Difference(a,b)[o] == Math#clip(a[o] - b[o]));
  lemma {:extract_pattern Multiplicity(Difference(a, b), o)} MultiplicityDifference(a: Multiset, b: Multiset, o: Box)
    ensures Multiplicity(Difference(a, b), o) == Math.Clip(Multiplicity(a, o) - Multiplicity(b, o))

  // axiom (forall a, b: MultiSet, y: Box :: { MultiSet#Difference(a, b), b[y], a[y] }
  //   a[y] <= b[y] ==> MultiSet#Difference(a, b)[y] == 0 );
  lemma {:extract_pattern Difference(a, b), Multiplicity(b, y), Multiplicity(a, y)} MultiplicityDifferenceOnDominant(a: Multiset, b: Multiset, y: Box)
    requires Multiplicity(a, y) <= Multiplicity(b, y)
    ensures Multiplicity(Difference(a, b), y) == 0

  // axiom (forall a, b: MultiSet ::
  //   { MultiSet#Card(MultiSet#Difference(a, b)) }
  //   MultiSet#Card(MultiSet#Difference(a, b)) + MultiSet#Card(MultiSet#Difference(b, a))
  //   + 2 * MultiSet#Card(MultiSet#Intersection(a, b))
  //     == MultiSet#Card(MultiSet#Union(a, b)) &&
  //   MultiSet#Card(MultiSet#Difference(a, b)) == MultiSet#Card(a) - MultiSet#Card(MultiSet#Intersection(a, b)));
  lemma {:extract_pattern Card(Difference(a, b))} CardDifference(a: Multiset, b: Multiset)
    ensures Card(Difference(a, b)) + Card(Difference(b, a)) + 2 * Card(Intersection(a, b)) == Card(Union(a, b))
    ensures Card(Difference(a, b)) == Card(a) - Card(Intersection(a, b))

  // // multiset subset means a must have at most as many of each element as b
  // function MultiSet#Subset(MultiSet, MultiSet): bool;
  predicate {:extract_boogie_name "MultiSet#Subset"} Subset(a: Multiset, b: Multiset)

  // axiom (forall a: MultiSet, b: MultiSet :: { MultiSet#Subset(a,b) }
  //   MultiSet#Subset(a,b) <==> (forall o: Box :: {a[o]} {b[o]} a[o] <= b[o]));
  lemma {:extract_pattern Subset(a, b)} SubsetDefinition(a: Multiset, b: Multiset)
    ensures Subset(a, b) <==> forall o {:extract_pattern Multiplicity(a, o)} {:extract_pattern Multiplicity(b, o)} :: Multiplicity(a, o) <= Multiplicity(b, o)

  // function MultiSet#Equal(MultiSet, MultiSet): bool;
  predicate {:extract_boogie_name "MultiSet#Equal"} Equal(a: Multiset, b: Multiset)

  // axiom (forall a: MultiSet, b: MultiSet :: { MultiSet#Equal(a,b) }
  //   MultiSet#Equal(a,b) <==> (forall o: Box :: {a[o]} {b[o]} a[o] == b[o]));
  lemma {:extract_pattern Equal(a, b)} EqualDefinition(a: Multiset, b: Multiset)
    ensures Equal(a, b) <==> forall o {:extract_pattern Multiplicity(a, o)} {:extract_pattern Multiplicity(b, o)} :: Multiplicity(a, o) == Multiplicity(b, o)

  // // extensionality axiom for multisets
  // axiom (forall a: MultiSet, b: MultiSet :: { MultiSet#Equal(a,b) }
  //   MultiSet#Equal(a,b) ==> a == b);
  lemma {:extract_pattern Equal(a, b)} Extensionality(a: Multiset, b: Multiset)
    requires Equal(a, b)
    ensures a == b

  // function MultiSet#Disjoint(MultiSet, MultiSet): bool;
  predicate {:extract_boogie_name "MultiSet#Disjoint"} Disjoint(a: Multiset, b: Multiset)

  // axiom (forall a: MultiSet, b: MultiSet :: { MultiSet#Disjoint(a,b) }
  //   MultiSet#Disjoint(a,b) <==> (forall o: Box :: {a[o]} {b[o]} a[o] == 0 || b[o] == 0));
  lemma {:extract_pattern Disjoint(a, b)} DisjointDefinition(a: Multiset, b: Multiset)
    ensures Disjoint(a, b) <==> forall o {:extract_pattern Multiplicity(a, o)} {:extract_pattern Multiplicity(b, o)} :: Multiplicity(a, o) == 0 || Multiplicity(b, o) == 0

  // // conversion to a multiset. each element in the original set has duplicity 1.
  // function MultiSet#FromSet(Set): MultiSet;
  function {:extract_boogie_name "MultiSet#FromSet"} FromSet(s: Sets.Set): Multiset

  // axiom (forall s: Set, a: Box :: { MultiSet#FromSet(s)[a] }
  //   (MultiSet#FromSet(s)[a] == 0 <==> !s[a]) &&
  //   (MultiSet#FromSet(s)[a] == 1 <==> s[a]));
  lemma {:extract_pattern Multiplicity(FromSet(s), a)} MultiplicityFromSet(s: Sets.Set, a: Box)
    ensures Multiplicity(FromSet(s), a) == 0 <==> !Sets.IsMember(s, a)
    ensures Multiplicity(FromSet(s), a) == 1 <==> Sets.IsMember(s, a)

  // axiom (forall s: Set :: { MultiSet#Card(MultiSet#FromSet(s)) }
  //   MultiSet#Card(MultiSet#FromSet(s)) == Set#Card(s));
  lemma {:extract_pattern Card(FromSet(s))} CardFromSet(s: Sets.Set)
    ensures Card(FromSet(s)) == Sets.Card(s)

  // // conversion to a multiset, from a sequence.
  // function MultiSet#FromSeq(Seq): MultiSet uses {
  //   axiom MultiSet#FromSeq(Seq#Empty(): Seq) == MultiSet#Empty(): MultiSet;
  // }
  function {:extract_boogie_name "MultiSet#FromSeq"} FromSeq(s: Sequences.Seq): Multiset

  lemma {:extract_used_by FromSeq} FromEmptySeq()
    ensures FromSeq(Sequences.Empty()) == Empty()

  // // conversion produces a good map.
  // axiom (forall s: Seq :: { MultiSet#FromSeq(s) } $IsGoodMultiSet(MultiSet#FromSeq(s)) );
  lemma {:extract_pattern FromSeq(s)} ConversionGivesGoodMultiset(s: Sequences.Seq)
    ensures IsGood(FromSeq(s))

  // // cardinality axiom
  // axiom (forall s: Seq ::
  //   { MultiSet#Card(MultiSet#FromSeq(s)) }
  //     MultiSet#Card(MultiSet#FromSeq(s)) == Seq#Length(s));
  lemma {:extract_pattern Card(FromSeq(s))} CardFromSeq(s: Sequences.Seq)
    ensures Card(FromSeq(s)) == Sequences.Length(s)

  // // building axiom
  // axiom (forall s: Seq, v: Box ::
  //   { MultiSet#FromSeq(Seq#Build(s, v)) }
  //     MultiSet#FromSeq(Seq#Build(s, v)) == MultiSet#UnionOne(MultiSet#FromSeq(s), v)
  //   );
  lemma {:extract_pattern FromSeq(Sequences.Build(s, v))} BuildFromSeq(s: Sequences.Seq, v: Box)
    ensures FromSeq(Sequences.Build(s, v)) == UnionOne(FromSeq(s), v)

  // // concatenation axiom
  // axiom (forall a: Seq, b: Seq ::
  //   { MultiSet#FromSeq(Seq#Append(a, b)) }
  //     MultiSet#FromSeq(Seq#Append(a, b)) == MultiSet#Union(MultiSet#FromSeq(a), MultiSet#FromSeq(b)) );
  lemma {:extract_pattern FromSeq(Sequences.Append(a, b))} Concatenation(a: Sequences.Seq, b: Sequences.Seq)
    ensures FromSeq(Sequences.Append(a, b)) == Union(FromSeq(a), FromSeq(b))

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

  // axiom (forall s: Seq, x: Box :: { MultiSet#FromSeq(s)[x] }
  //   (exists i : int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && x == Seq#Index(s,i)) <==> 0 < MultiSet#FromSeq(s)[x] );
  lemma {:extract_pattern Multiplicity(FromSeq(s), x)} MultiplicityFromSeq(s: Sequences.Seq, x: Box)
    ensures exists i {:extract_pattern Sequences.Index(s, i)} ::
      0 <= i < Sequences.Length(s) && x == Sequences.Index(s, i) <==> 0 < Multiplicity(FromSeq(s), x)
}
