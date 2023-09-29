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

type {:builtin "Seq"} BuiltinSeq _;
type Seq = BuiltinSeq Box;

function {:builtin "seq.empty"} Seq_Empty(): Seq;
function {:builtin "seq.len"} Seq_Len(a: Seq): int;
function {:builtin "seq.++"} Seq_Concat(a: Seq, b: Seq): Seq;
function {:builtin "seq.unit"} Seq_Unit(v: Box): Seq;
function {:builtin "seq.nth"} Seq_Nth(a: Seq, i: int): Box;
function {:builtin "seq.extract"} Seq_Extract(a: Seq, pos: int, length: int): Seq;
function {:builtin "seq.contains"} Seq_Contains(s1: Seq, s2: Seq): bool;

function
#if SEQ_INLINE
{:inline}
#endif
Seq#Length(s: Seq) : int {
  Seq_Len(s)
}

function
#if SEQ_INLINE
{:inline}
#endif
Seq#Empty() : Seq {
  Seq_Empty()
}

function
#if SEQ_INLINE
{:inline}
#endif
Seq#Singleton(v: Box) : Seq {
  Seq_Unit(v)
}

function
#if SEQ_INLINE
{:inline}
#endif
Seq#Append(s1: Seq, s2: Seq) : Seq {
    Seq_Concat(s1, s2)
}

function
#if SEQ_INLINE
{:inline}
#endif
Seq#Index(s: Seq, i: int) : Box {
  Seq_Nth(s, i)
}

function
#if SEQ_INLINE
{:inline}
#endif
Seq#Update(s: Seq, i: int, v: Box) : Seq {
  Seq_Concat(Seq_Extract(s, 0, i), Seq_Concat(Seq_Unit(v), Seq_Extract(s, i + 1, Seq_Len(s) - i - 1)))
}

function
#if SEQ_INLINE
{:inline}
#endif
Seq#Contains(s: Seq, v: Box) : bool {
  Seq_Contains(s, Seq_Unit(v))
}

function
#if SEQ_INLINE
{:inline}
#endif
Seq#Equal(s1: Seq, s2: Seq) : bool {
    s1 == s2
}

function
#if SEQ_INLINE
{:inline}
#endif
Seq#Build(s: Seq, v: Box): Seq {
  Seq_Concat(s, Seq_Unit(v))
}

function
#if SEQ_INLINE
{:inline}
#endif
Seq#SameUntil(s1: Seq, s2: Seq, n: int): bool {
  Seq_Extract(s1, 0, n) == Seq_Extract(s2, 0, n)
}

function
#if SEQ_INLINE
{:inline}
#endif
Seq#Take(s: Seq, howMany: int): Seq {
  Seq_Extract(s, 0, howMany)
}

function
#if SEQ_INLINE
{:inline}
#endif
Seq#Drop(s: Seq, howMany: int): Seq {
  Seq_Extract(s, howMany, Seq_Len(s) - howMany)
}

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

// Extension axiom, triggers only on Takes from arrays.
axiom (forall h: Heap, a: ref, n0, n1: int ::
        { Seq#Take(Seq#FromArray(h, a), n0), Seq#Take(Seq#FromArray(h, a), n1) }
        n0 + 1 == n1 && 0 <= n0 && n1 <= _System.array.Length(a) ==> Seq#Take(Seq#FromArray(h, a), n1) == Seq#Build(Seq#Take(Seq#FromArray(h, a), n0), read(h, a, IndexField(n0): Field Box)) );

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

// -------------------------------------------------------------------------
