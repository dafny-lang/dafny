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

function TSeq(Ty) : Ty;
function Inv0_TSeq(Ty) : Ty;
axiom (forall t: Ty :: { TSeq(t) } Inv0_TSeq(TSeq(t)) == t);
axiom (forall t: Ty :: { TSeq(t) } Tag(TSeq(t)) == TagSeq);

const unique TagSeq: TyTag;

// ---------------------------------------------------------------
// -- Is and IsAlloc ---------------------------------------------
// ---------------------------------------------------------------

axiom (forall v: Seq, t0: Ty :: { $Is(v, TSeq(t0)) }
  $Is(v, TSeq(t0)) <==>
  (forall i : int :: { Seq#Index(v, i) }
    0 <= i && i < Seq#Length(v) ==>
    $IsBox(Seq#Index(v, i), t0)));

axiom (forall v: Seq, t0: Ty, h: Heap :: { $IsAlloc(v, TSeq(t0), h) }
  $IsAlloc(v, TSeq(t0), h) <==>
  (forall i : int :: { Seq#Index(v, i) }
    0 <= i && i < Seq#Length(v) ==>
	$IsAllocBox(Seq#Index(v, i), t0, h)));

// ---------------------------------------------------------------
// -- Boxing and unboxing ----------------------------------------
// ---------------------------------------------------------------

axiom (forall bx : Box, t : Ty ::
    { $IsBox(bx, TSeq(t)) }
    ( $IsBox(bx, TSeq(t)) ==> $Box($Unbox(bx) : Seq) == bx && $Is($Unbox(bx) : Seq, TSeq(t))));

// ---------------------------------------------------------------
// -- Axiomatization of sequences --------------------------------
// ---------------------------------------------------------------

type Seq;

function Seq#Length(Seq): int;
axiom (forall s: Seq :: { Seq#Length(s) } 0 <= Seq#Length(s));

function Seq#Empty(): Seq uses {
  axiom (Seq#Length(Seq#Empty(): Seq) == 0);
}
axiom (forall s: Seq :: { Seq#Length(s) }
  (Seq#Length(s) == 0 ==> s == Seq#Empty())
// The following would be a nice fact to include, because it would enable verifying the
// GenericPick.SeqPick* methods in Test/dafny0/SmallTests.dfy.  However, it substantially
// slows down performance on some other tests, including running seemingly forever on
// some.
//  && (Seq#Length(s) != 0 ==> (exists x: Box :: Seq#Contains(s, x)))
  );

// The empty sequence $Is any type
//axiom (forall t: Ty :: {$Is(Seq#Empty(): Seq, TSeq(t))} $Is(Seq#Empty(): Seq, TSeq(t)));

function Seq#Singleton(Box): Seq;
axiom (forall t: Box :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);

function Seq#Build(s: Seq, val: Box): Seq;
function Seq#Build_inv0(s: Seq) : Seq;
function Seq#Build_inv1(s: Seq) : Box;
axiom (forall s: Seq, val: Box ::
  { Seq#Build(s, val) }
  Seq#Build_inv0(Seq#Build(s, val)) == s &&
  Seq#Build_inv1(Seq#Build(s, val)) == val);

axiom (forall s: Seq, v: Box ::
  { Seq#Build(s,v) }
  Seq#Length(Seq#Build(s,v)) == 1 + Seq#Length(s));
axiom (forall s: Seq, i: int, v: Box :: { Seq#Index(Seq#Build(s,v), i) }
  (i == Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == v) &&
  (i != Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == Seq#Index(s, i)));

// Build preserves $Is
axiom (forall s: Seq, bx: Box, t: Ty :: { $Is(Seq#Build(s,bx),TSeq(t)) }
    $Is(s,TSeq(t)) && $IsBox(bx,t) ==> $Is(Seq#Build(s,bx),TSeq(t)));

function Seq#Create(ty: Ty, heap: Heap, len: int, init: HandleType): Seq;
axiom (forall ty: Ty, heap: Heap, len: int, init: HandleType ::
  { Seq#Length(Seq#Create(ty, heap, len, init): Seq) }
  $IsGoodHeap(heap) && 0 <= len ==>
  Seq#Length(Seq#Create(ty, heap, len, init): Seq) == len);
axiom (forall ty: Ty, heap: Heap, len: int, init: HandleType, i: int ::
  { Seq#Index(Seq#Create(ty, heap, len, init), i) }
  $IsGoodHeap(heap) && 0 <= i && i < len ==>
  Seq#Index(Seq#Create(ty, heap, len, init), i) == Apply1(TInt, ty, heap, init, $Box(i)));

function Seq#Append(Seq, Seq): Seq;
axiom (forall s0: Seq, s1: Seq :: { Seq#Length(Seq#Append(s0,s1)) }
  Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));

function Seq#Index(Seq, int): Box;
axiom (forall t: Box :: { Seq#Index(Seq#Singleton(t), 0) } Seq#Index(Seq#Singleton(t), 0) == t);
axiom (forall s0: Seq, s1: Seq, n: int :: { Seq#Index(Seq#Append(s0,s1), n) }
  (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)) &&
  (Seq#Length(s0) <= n ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, n - Seq#Length(s0))));

function Seq#Update(Seq, int, Box): Seq;
axiom (forall s: Seq, i: int, v: Box :: { Seq#Length(Seq#Update(s,i,v)) }
  0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s,i,v)) == Seq#Length(s));
axiom (forall s: Seq, i: int, v: Box, n: int :: { Seq#Index(Seq#Update(s,i,v),n) }
  0 <= n && n < Seq#Length(s) ==>
    (i == n ==> Seq#Index(Seq#Update(s,i,v),n) == v) &&
    (i != n ==> Seq#Index(Seq#Update(s,i,v),n) == Seq#Index(s,n)));

function Seq#Contains(Seq, Box): bool;
axiom (forall s: Seq, x: Box :: { Seq#Contains(s,x) }
  Seq#Contains(s,x) <==>
    (exists i: int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && Seq#Index(s,i) == x));
axiom (forall x: Box ::
  { Seq#Contains(Seq#Empty(), x) }
  !Seq#Contains(Seq#Empty(), x));

axiom (forall s0: Seq, s1: Seq, x: Box ::
  { Seq#Contains(Seq#Append(s0, s1), x) }
  Seq#Contains(Seq#Append(s0, s1), x) <==>
    Seq#Contains(s0, x) || Seq#Contains(s1, x));

axiom (forall s: Seq, v: Box, x: Box ::  // needed to prove things like '4 in [2,3,4]', see method TestSequences0 in SmallTests.dfy
  { Seq#Contains(Seq#Build(s, v), x) }
    Seq#Contains(Seq#Build(s, v), x) <==> (v == x || Seq#Contains(s, x)));

axiom (forall s: Seq, n: int, x: Box ::
  { Seq#Contains(Seq#Take(s, n), x) }
  Seq#Contains(Seq#Take(s, n), x) <==>
    (exists i: int :: { Seq#Index(s, i) }
      0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));
axiom (forall s: Seq, n: int, x: Box ::
  { Seq#Contains(Seq#Drop(s, n), x) }
  Seq#Contains(Seq#Drop(s, n), x) <==>
    (exists i: int :: { Seq#Index(s, i) }
      0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

function Seq#Equal(Seq, Seq): bool;
axiom (forall s0: Seq, s1: Seq :: { Seq#Equal(s0,s1) }
  Seq#Equal(s0,s1) <==>
    Seq#Length(s0) == Seq#Length(s1) &&
    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0,j) == Seq#Index(s1,j)));
axiom (forall a: Seq, b: Seq :: { Seq#Equal(a,b) }  // extensionality axiom for sequences
  Seq#Equal(a,b) ==> a == b);

function Seq#SameUntil(Seq, Seq, int): bool;
axiom (forall s0: Seq, s1: Seq, n: int :: { Seq#SameUntil(s0,s1,n) }
  Seq#SameUntil(s0,s1,n) <==>
    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        0 <= j && j < n ==> Seq#Index(s0,j) == Seq#Index(s1,j)));

function Seq#Take(s: Seq, howMany: int): Seq;
axiom (forall s: Seq, n: int :: { Seq#Length(Seq#Take(s,n)) }
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n);
axiom (forall s: Seq, n: int, j: int ::
  {:weight 25}
  { Seq#Index(Seq#Take(s,n), j) }
  { Seq#Index(s, j), Seq#Take(s,n) }
  0 <= j && j < n && j < Seq#Length(s) ==>
    Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));

function Seq#Drop(s: Seq, howMany: int): Seq;
axiom (forall s: Seq, n: int :: { Seq#Length(Seq#Drop(s,n)) }
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n);
axiom (forall s: Seq, n: int, j: int ::
  {:weight 25}
  { Seq#Index(Seq#Drop(s,n), j) }
  0 <= n && 0 <= j && j < Seq#Length(s)-n ==>
    Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, j+n));
axiom (forall s: Seq, n: int, k: int ::
  {:weight 25}
  { Seq#Index(s, k), Seq#Drop(s,n) }
  0 <= n && n <= k && k < Seq#Length(s) ==>
    Seq#Index(Seq#Drop(s,n), k-n) == Seq#Index(s, k));

axiom (forall s, t: Seq, n: int ::
  { Seq#Take(Seq#Append(s, t), n) }
  { Seq#Drop(Seq#Append(s, t), n) }
  n == Seq#Length(s)
  ==>
  Seq#Take(Seq#Append(s, t), n) == s &&
  Seq#Drop(Seq#Append(s, t), n) == t);

function Seq#FromArray(h: Heap, a: ref): Seq;
axiom (forall h: Heap, a: ref ::
  { Seq#Length(Seq#FromArray(h,a)) }
  Seq#Length(Seq#FromArray(h, a)) == _System.array.Length(a));
axiom (forall h: Heap, a: ref ::
  { Seq#FromArray(h, a) }
  (forall i: int ::
    // it's important to include both triggers, so that assertions about the
    // the relation between the array and the sequence can be proved in either
    // direction
    { read(h, a, IndexField(i)) }
    { Seq#Index(Seq#FromArray(h, a): Seq, i) }
    0 <= i &&
    i < Seq#Length(Seq#FromArray(h, a))  // this will trigger the previous axiom to get a connection with _System.array.Length(a)
    ==>
    Seq#Index(Seq#FromArray(h, a), i) == read(h, a, IndexField(i))));
axiom (forall h0, h1: Heap, a: ref ::
  { Seq#FromArray(h1, a), $HeapSucc(h0, h1) }
  $IsGoodHeap(h0) && $IsGoodHeap(h1) && $HeapSucc(h0, h1) && h0[a] == h1[a]
  ==>
  Seq#FromArray(h0, a) == Seq#FromArray(h1, a));
axiom (forall h: Heap, i: int, v: Box, a: ref ::
  { Seq#FromArray(update(h, a, IndexField(i), v), a) }
    0 <= i && i < _System.array.Length(a) ==> Seq#FromArray(update(h, a, IndexField(i), v), a) == Seq#Update(Seq#FromArray(h, a), i, v) );

// Commutability of Take and Drop with Update.
axiom (forall s: Seq, i: int, v: Box, n: int ::
        { Seq#Take(Seq#Update(s, i, v), n) }
        0 <= i && i < n && n <= Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v) );
axiom (forall s: Seq, i: int, v: Box, n: int ::
        { Seq#Take(Seq#Update(s, i, v), n) }
        n <= i && i < Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));
axiom (forall s: Seq, i: int, v: Box, n: int ::
        { Seq#Drop(Seq#Update(s, i, v), n) }
        0 <= n && n <= i && i < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i-n, v) );
axiom (forall s: Seq, i: int, v: Box, n: int ::
        { Seq#Drop(Seq#Update(s, i, v), n) }
        0 <= i && i < n && n <= Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));
// Extension axiom, triggers only on Takes from arrays.
axiom (forall h: Heap, a: ref, n0, n1: int ::
        { Seq#Take(Seq#FromArray(h, a), n0), Seq#Take(Seq#FromArray(h, a), n1) }
        n0 + 1 == n1 && 0 <= n0 && n1 <= _System.array.Length(a) ==> Seq#Take(Seq#FromArray(h, a), n1) == Seq#Build(Seq#Take(Seq#FromArray(h, a), n0), read(h, a, IndexField(n0): Field Box)) );
// drop commutes with build.
axiom (forall s: Seq, v: Box, n: int ::
        { Seq#Drop(Seq#Build(s, v), n) }
        0 <= n && n <= Seq#Length(s) ==> Seq#Drop(Seq#Build(s, v), n) == Seq#Build(Seq#Drop(s, n), v) );

function Seq#Rank(Seq): int;
axiom (forall s: Seq, i: int ::
        { DtRank($Unbox(Seq#Index(s, i)): DatatypeType) }
        0 <= i && i < Seq#Length(s) ==> DtRank($Unbox(Seq#Index(s, i)): DatatypeType) < Seq#Rank(s) );
axiom (forall s: Seq, i: int ::
        { Seq#Rank(Seq#Drop(s, i)) }
        0 < i && i <= Seq#Length(s) ==> Seq#Rank(Seq#Drop(s, i)) < Seq#Rank(s) );
axiom (forall s: Seq, i: int ::
        { Seq#Rank(Seq#Take(s, i)) }
        0 <= i && i < Seq#Length(s) ==> Seq#Rank(Seq#Take(s, i)) < Seq#Rank(s) );
axiom (forall s: Seq, i: int, j: int ::
        { Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) }
        0 <= i && i < j && j <= Seq#Length(s) ==> Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) < Seq#Rank(s) );

// Additional axioms about common things
axiom (forall s: Seq, n: int :: { Seq#Drop(s, n) }
        n == 0 ==> Seq#Drop(s, n) == s);
axiom (forall s: Seq, n: int :: { Seq#Take(s, n) }
        n == 0 ==> Seq#Take(s, n) == Seq#Empty());
axiom (forall s: Seq, m, n: int :: { Seq#Drop(Seq#Drop(s, m), n) }
        0 <= m && 0 <= n && m+n <= Seq#Length(s) ==>
        Seq#Drop(Seq#Drop(s, m), n) == Seq#Drop(s, m+n));
