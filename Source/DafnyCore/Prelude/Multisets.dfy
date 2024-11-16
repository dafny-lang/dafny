module Multisets {
  // type MultiSet = [Box]int;

  // function $IsGoodMultiSet(ms: MultiSet): bool;
  // // ints are non-negative, used after havocing, and for conversion from sequences to multisets.
  // axiom (forall ms: MultiSet :: { $IsGoodMultiSet(ms) }
  //   $IsGoodMultiSet(ms) <==>
  //   (forall bx: Box :: { ms[bx] } 0 <= ms[bx] && ms[bx] <= MultiSet#Card(ms)));

  // function MultiSet#Card(MultiSet): int;
  // axiom (forall s: MultiSet :: { MultiSet#Card(s) } 0 <= MultiSet#Card(s));
  // axiom (forall s: MultiSet, x: Box, n: int :: { MultiSet#Card(s[x := n]) }
  //   0 <= n ==> MultiSet#Card(s[x := n]) == MultiSet#Card(s) - s[x] + n);

  // function MultiSet#Empty(): MultiSet;
  // axiom (forall o: Box :: { MultiSet#Empty()[o] } MultiSet#Empty()[o] == 0);
  // axiom (forall s: MultiSet :: { MultiSet#Card(s) }
  //   (MultiSet#Card(s) == 0 <==> s == MultiSet#Empty()) &&
  //   (MultiSet#Card(s) != 0 ==> (exists x: Box :: 0 < s[x])));

  // function MultiSet#Singleton(Box): MultiSet;
  // axiom (forall r: Box, o: Box :: { MultiSet#Singleton(r)[o] } (MultiSet#Singleton(r)[o] == 1 <==> r == o) &&
  //                                                             (MultiSet#Singleton(r)[o] == 0 <==> r != o));
  // axiom (forall r: Box :: { MultiSet#Singleton(r) } MultiSet#Singleton(r) == MultiSet#UnionOne(MultiSet#Empty(), r));

  // function MultiSet#UnionOne(MultiSet, Box): MultiSet;
  // // pure containment axiom (in the original multiset or is the added element)
  // axiom (forall a: MultiSet, x: Box, o: Box :: { MultiSet#UnionOne(a,x)[o] }
  //   0 < MultiSet#UnionOne(a,x)[o] <==> o == x || 0 < a[o]);
  // // union-ing increases count by one
  // axiom (forall a: MultiSet, x: Box :: { MultiSet#UnionOne(a, x) }
  //   MultiSet#UnionOne(a, x)[x] == a[x] + 1);
  // // non-decreasing
  // axiom (forall a: MultiSet, x: Box, y: Box :: { MultiSet#UnionOne(a, x), a[y] }
  //   0 < a[y] ==> 0 < MultiSet#UnionOne(a, x)[y]);
  // // other elements unchanged
  // axiom (forall a: MultiSet, x: Box, y: Box :: { MultiSet#UnionOne(a, x), a[y] }
  //   x != y ==> a[y] == MultiSet#UnionOne(a, x)[y]);
  // axiom (forall a: MultiSet, x: Box :: { MultiSet#Card(MultiSet#UnionOne(a, x)) }
  //   MultiSet#Card(MultiSet#UnionOne(a, x)) == MultiSet#Card(a) + 1);


  // function MultiSet#Union(MultiSet, MultiSet): MultiSet;
  // // union-ing is the sum of the contents
  // axiom (forall a: MultiSet, b: MultiSet, o: Box :: { MultiSet#Union(a,b)[o] }
  //   MultiSet#Union(a,b)[o] == a[o] + b[o]);
  // axiom (forall a: MultiSet, b: MultiSet :: { MultiSet#Card(MultiSet#Union(a,b)) }
  //   MultiSet#Card(MultiSet#Union(a,b)) == MultiSet#Card(a) + MultiSet#Card(b));

  // function MultiSet#Intersection(MultiSet, MultiSet): MultiSet;
  // axiom (forall a: MultiSet, b: MultiSet, o: Box :: { MultiSet#Intersection(a,b)[o] }
  //   MultiSet#Intersection(a,b)[o] == Math#min(a[o],  b[o]));

  // // left and right pseudo-idempotence
  // axiom (forall a, b: MultiSet :: { MultiSet#Intersection(MultiSet#Intersection(a, b), b) }
  //   MultiSet#Intersection(MultiSet#Intersection(a, b), b) == MultiSet#Intersection(a, b));
  // axiom (forall a, b: MultiSet :: { MultiSet#Intersection(a, MultiSet#Intersection(a, b)) }
  //   MultiSet#Intersection(a, MultiSet#Intersection(a, b)) == MultiSet#Intersection(a, b));

  // // multiset difference, a - b. clip() makes it positive.
  // function MultiSet#Difference(MultiSet, MultiSet): MultiSet;
  // axiom (forall a: MultiSet, b: MultiSet, o: Box :: { MultiSet#Difference(a,b)[o] }
  //   MultiSet#Difference(a,b)[o] == Math#clip(a[o] - b[o]));
  // axiom (forall a, b: MultiSet, y: Box :: { MultiSet#Difference(a, b), b[y], a[y] }
  //   a[y] <= b[y] ==> MultiSet#Difference(a, b)[y] == 0 );
  // axiom (forall a, b: MultiSet ::
  //   { MultiSet#Card(MultiSet#Difference(a, b)) }
  //   MultiSet#Card(MultiSet#Difference(a, b)) + MultiSet#Card(MultiSet#Difference(b, a))
  //   + 2 * MultiSet#Card(MultiSet#Intersection(a, b))
  //     == MultiSet#Card(MultiSet#Union(a, b)) &&
  //   MultiSet#Card(MultiSet#Difference(a, b)) == MultiSet#Card(a) - MultiSet#Card(MultiSet#Intersection(a, b)));

  // // multiset subset means a must have at most as many of each element as b
  // function MultiSet#Subset(MultiSet, MultiSet): bool;
  // axiom (forall a: MultiSet, b: MultiSet :: { MultiSet#Subset(a,b) }
  //   MultiSet#Subset(a,b) <==> (forall o: Box :: {a[o]} {b[o]} a[o] <= b[o]));

  // function MultiSet#Equal(MultiSet, MultiSet): bool;
  // axiom (forall a: MultiSet, b: MultiSet :: { MultiSet#Equal(a,b) }
  //   MultiSet#Equal(a,b) <==> (forall o: Box :: {a[o]} {b[o]} a[o] == b[o]));
  // // extensionality axiom for multisets
  // axiom (forall a: MultiSet, b: MultiSet :: { MultiSet#Equal(a,b) }
  //   MultiSet#Equal(a,b) ==> a == b);

  // function MultiSet#Disjoint(MultiSet, MultiSet): bool;
  // axiom (forall a: MultiSet, b: MultiSet :: { MultiSet#Disjoint(a,b) }
  //   MultiSet#Disjoint(a,b) <==> (forall o: Box :: {a[o]} {b[o]} a[o] == 0 || b[o] == 0));

  // // conversion to a multiset. each element in the original set has duplicity 1.
  // function MultiSet#FromSet(Set): MultiSet;
  // axiom (forall s: Set, a: Box :: { MultiSet#FromSet(s)[a] }
  //   (MultiSet#FromSet(s)[a] == 0 <==> !s[a]) &&
  //   (MultiSet#FromSet(s)[a] == 1 <==> s[a]));
  // axiom (forall s: Set :: { MultiSet#Card(MultiSet#FromSet(s)) }
  //   MultiSet#Card(MultiSet#FromSet(s)) == Set#Card(s));

  // // conversion to a multiset, from a sequence.
  // function MultiSet#FromSeq(Seq): MultiSet uses {
  //   axiom MultiSet#FromSeq(Seq#Empty(): Seq) == MultiSet#Empty(): MultiSet;
  // }

  // // conversion produces a good map.
  // axiom (forall s: Seq :: { MultiSet#FromSeq(s) } $IsGoodMultiSet(MultiSet#FromSeq(s)) );
  // // cardinality axiom
  // axiom (forall s: Seq ::
  //   { MultiSet#Card(MultiSet#FromSeq(s)) }
  //     MultiSet#Card(MultiSet#FromSeq(s)) == Seq#Length(s));
  // // building axiom
  // axiom (forall s: Seq, v: Box ::
  //   { MultiSet#FromSeq(Seq#Build(s, v)) }
  //     MultiSet#FromSeq(Seq#Build(s, v)) == MultiSet#UnionOne(MultiSet#FromSeq(s), v)
  //   );

  // // concatenation axiom
  // axiom (forall a: Seq, b: Seq ::
  //   { MultiSet#FromSeq(Seq#Append(a, b)) }
  //     MultiSet#FromSeq(Seq#Append(a, b)) == MultiSet#Union(MultiSet#FromSeq(a), MultiSet#FromSeq(b)) );

  // // update axiom
  // axiom (forall s: Seq, i: int, v: Box, x: Box ::
  //   { MultiSet#FromSeq(Seq#Update(s, i, v))[x] }
  //     0 <= i && i < Seq#Length(s) ==>
  //     MultiSet#FromSeq(Seq#Update(s, i, v))[x] ==
  //       MultiSet#Union(MultiSet#Difference(MultiSet#FromSeq(s), MultiSet#Singleton(Seq#Index(s,i))), MultiSet#Singleton(v))[x] );
  //   // i.e. MS(Update(s, i, v)) == MS(s) - {{s[i]}} + {{v}}
  // axiom (forall s: Seq, x: Box :: { MultiSet#FromSeq(s)[x] }
  //   (exists i : int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && x == Seq#Index(s,i)) <==> 0 < MultiSet#FromSeq(s)[x] );
}
