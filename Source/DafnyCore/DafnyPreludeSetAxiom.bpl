// Dafny prelude
// Created 9 February 2008 by Rustan Leino.
// Converted to Boogie 2 on 28 June 2008.
// Edited sequence axioms 20 October 2009 by Alex Summers.
// Modified 2014 by Dan Rosen.
// Copyright (c) 2008-2014, Microsoft.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

// ---------------------------------------------------------------
// -- Types ------------------------------------------------------
// ---------------------------------------------------------------

function TSet(Ty): Ty;
function Inv0_TSet(Ty) : Ty;
axiom (forall t: Ty :: { TSet(t) } Inv0_TSet(TSet(t)) == t);
axiom (forall t: Ty :: { TSet(t) } Tag(TSet(t)) == TagSet);

const unique TagSet: TyTag;

// ---------------------------------------------------------------
// -- Is and IsAlloc ---------------------------------------------
// ---------------------------------------------------------------

axiom (forall v: Set, t0: Ty :: { $Is(v, TSet(t0)) }
  $Is(v, TSet(t0)) <==>
  (forall bx: Box :: { v[bx] }
    v[bx] ==> $IsBox(bx, t0)));

axiom (forall v: Set, t0: Ty, h: Heap :: { $IsAlloc(v, TSet(t0), h) }
  $IsAlloc(v, TSet(t0), h) <==>
  (forall bx: Box :: { v[bx] }
    v[bx] ==> $IsAllocBox(bx, t0, h)));

// ---------------------------------------------------------------
// -- Boxing and unboxing ----------------------------------------
// ---------------------------------------------------------------

axiom (forall bx : Box, t : Ty ::
    { $IsBox(bx, TSet(t)) }
    ( $IsBox(bx, TSet(t)) ==> $Box($Unbox(bx) : Set) == bx && $Is($Unbox(bx) : Set, TSet(t))));

// ---------------------------------------------------------------
// -- Axiomatization of sets -------------------------------------
// ---------------------------------------------------------------

type Set = [Box]bool;

function Set#Card(Set): int;
axiom (forall s: Set :: { Set#Card(s) } 0 <= Set#Card(s));

function Set#Empty(): Set;
axiom (forall o: Box :: { Set#Empty()[o] } !Set#Empty()[o]);
axiom (forall s: Set :: { Set#Card(s) }
  (Set#Card(s) == 0 <==> s == Set#Empty()) &&
  (Set#Card(s) != 0 ==> (exists x: Box :: s[x])));

// the empty set could be of anything
//axiom (forall t: Ty :: { $Is(Set#Empty() : [Box]bool, TSet(t)) } $Is(Set#Empty() : [Box]bool, TSet(t)));

function Set#Singleton(Box): Set;
axiom (forall r: Box :: { Set#Singleton(r) } Set#Singleton(r)[r]);
axiom (forall r: Box, o: Box :: { Set#Singleton(r)[o] } Set#Singleton(r)[o] <==> r == o);
axiom (forall r: Box :: { Set#Card(Set#Singleton(r)) } Set#Card(Set#Singleton(r)) == 1);

function Set#UnionOne(Set, Box): Set;
axiom (forall a: Set, x: Box, o: Box :: { Set#UnionOne(a,x)[o] }
  Set#UnionOne(a,x)[o] <==> o == x || a[o]);
axiom (forall a: Set, x: Box :: { Set#UnionOne(a, x) }
  Set#UnionOne(a, x)[x]);
axiom (forall a: Set, x: Box, y: Box :: { Set#UnionOne(a, x), a[y] }
  a[y] ==> Set#UnionOne(a, x)[y]);
axiom (forall a: Set, x: Box :: { Set#Card(Set#UnionOne(a, x)) }
  a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a));
axiom (forall a: Set, x: Box :: { Set#Card(Set#UnionOne(a, x)) }
  !a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a) + 1);

function Set#Union(Set, Set): Set;
axiom (forall a: Set, b: Set, o: Box :: { Set#Union(a,b)[o] }
  Set#Union(a,b)[o] <==> a[o] || b[o]);
axiom (forall a, b: Set, y: Box :: { Set#Union(a, b), a[y] }
  a[y] ==> Set#Union(a, b)[y]);
axiom (forall a, b: Set, y: Box :: { Set#Union(a, b), b[y] }
  b[y] ==> Set#Union(a, b)[y]);
axiom (forall a, b: Set :: { Set#Union(a, b) }
  Set#Disjoint(a, b) ==>
    Set#Difference(Set#Union(a, b), a) == b &&
    Set#Difference(Set#Union(a, b), b) == a);
// Follows from the general union axiom, but might be still worth including, because disjoint union is a common case:
// axiom (forall a, b: Set :: { Set#Card(Set#Union(a, b)) }
//   Set#Disjoint(a, b) ==>
//     Set#Card(Set#Union(a, b)) == Set#Card(a) + Set#Card(b));

function Set#Intersection(Set, Set): Set;
axiom (forall a: Set, b: Set, o: Box :: { Set#Intersection(a,b)[o] }
  Set#Intersection(a,b)[o] <==> a[o] && b[o]);

axiom (forall a, b: Set :: { Set#Union(Set#Union(a, b), b) }
  Set#Union(Set#Union(a, b), b) == Set#Union(a, b));
axiom (forall a, b: Set :: { Set#Union(a, Set#Union(a, b)) }
  Set#Union(a, Set#Union(a, b)) == Set#Union(a, b));
axiom (forall a, b: Set :: { Set#Intersection(Set#Intersection(a, b), b) }
  Set#Intersection(Set#Intersection(a, b), b) == Set#Intersection(a, b));
axiom (forall a, b: Set :: { Set#Intersection(a, Set#Intersection(a, b)) }
  Set#Intersection(a, Set#Intersection(a, b)) == Set#Intersection(a, b));
axiom (forall a, b: Set :: { Set#Card(Set#Union(a, b)) }{ Set#Card(Set#Intersection(a, b)) }
  Set#Card(Set#Union(a, b)) + Set#Card(Set#Intersection(a, b)) == Set#Card(a) + Set#Card(b));

function Set#Difference(Set, Set): Set;
axiom (forall a: Set, b: Set, o: Box :: { Set#Difference(a,b)[o] }
  Set#Difference(a,b)[o] <==> a[o] && !b[o]);
axiom (forall a, b: Set, y: Box :: { Set#Difference(a, b), b[y] }
  b[y] ==> !Set#Difference(a, b)[y] );
axiom (forall a, b: Set ::
  { Set#Card(Set#Difference(a, b)) }
  Set#Card(Set#Difference(a, b)) + Set#Card(Set#Difference(b, a))
  + Set#Card(Set#Intersection(a, b))
    == Set#Card(Set#Union(a, b)) &&
  Set#Card(Set#Difference(a, b)) == Set#Card(a) - Set#Card(Set#Intersection(a, b)));

function Set#Subset(Set, Set): bool;
axiom (forall a: Set, b: Set :: { Set#Subset(a,b) }
  Set#Subset(a,b) <==> (forall o: Box :: {a[o]} {b[o]} a[o] ==> b[o]));
// axiom(forall a: Set, b: Set ::
//   { Set#Subset(a,b), Set#Card(a), Set#Card(b) }  // very restrictive trigger
//   Set#Subset(a,b) ==> Set#Card(a) <= Set#Card(b));


function Set#Equal(Set, Set): bool;
axiom (forall a: Set, b: Set :: { Set#Equal(a,b) }
  Set#Equal(a,b) <==> (forall o: Box :: {a[o]} {b[o]} a[o] <==> b[o]));
axiom (forall a: Set, b: Set :: { Set#Equal(a,b) }  // extensionality axiom for sets
  Set#Equal(a,b) ==> a == b);

function Set#Disjoint(Set, Set): bool;
axiom (forall a: Set, b: Set :: { Set#Disjoint(a,b) }
  Set#Disjoint(a,b) <==> (forall o: Box :: {a[o]} {b[o]} !a[o] || !b[o]));
