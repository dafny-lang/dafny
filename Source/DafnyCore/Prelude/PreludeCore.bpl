// Dafny prelude
// Created 9 February 2008 by Rustan Leino.
// Converted to Boogie 2 on 28 June 2008.
// Edited sequence axioms 20 October 2009 by Alex Summers.
// Modified 2014 by Dan Rosen.
// Copyright (c) 2008-2014, Microsoft.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

const $$Language$Dafny: bool uses {  // To be recognizable to the ModelViewer as
  axiom $$Language$Dafny;            // coming from a Dafny program.
}

// ---------------------------------------------------------------
// -- Types ------------------------------------------------------
// ---------------------------------------------------------------

type Ty;
type Bv0 = int;

const unique TBool : Ty uses {
  axiom Tag(TBool) == TagBool;
}
const unique TChar : Ty uses {
  axiom Tag(TChar) == TagChar;
}
const unique TInt  : Ty uses {
  axiom Tag(TInt) == TagInt;
}
const unique TReal : Ty uses {
  axiom Tag(TReal) == TagReal;
}
const unique TORDINAL  : Ty uses {
  axiom Tag(TORDINAL) == TagORDINAL;
}
// See for which axioms we can make use of the trigger to determine the connection.
function TBitvector(int) : Ty;
axiom (forall w: int :: { TBitvector(w) } Inv0_TBitvector(TBitvector(w)) == w);

function TSet(Ty) : Ty;
axiom (forall t: Ty :: { TSet(t) } Inv0_TSet(TSet(t)) == t);
axiom (forall t: Ty :: { TSet(t) }      Tag(TSet(t))      == TagSet);

function TISet(Ty) : Ty;
axiom (forall t: Ty :: { TISet(t) } Inv0_TISet(TISet(t)) == t);
axiom (forall t: Ty :: { TISet(t) }     Tag(TISet(t))     == TagISet);

function TMultiSet(Ty) : Ty;
axiom (forall t: Ty :: { TMultiSet(t) } Inv0_TMultiSet(TMultiSet(t)) == t);
axiom (forall t: Ty :: { TMultiSet(t) } Tag(TMultiSet(t)) == TagMultiSet);

function TSeq(Ty) : Ty;
axiom (forall t: Ty :: { TSeq(t) } Inv0_TSeq(TSeq(t)) == t);
axiom (forall t: Ty :: { TSeq(t) } Tag(TSeq(t)) == TagSeq);

function TMap(Ty, Ty) : Ty;
axiom (forall t, u: Ty :: { TMap(t,u) } Inv0_TMap(TMap(t,u)) == t);
axiom (forall t, u: Ty :: { TMap(t,u) } Inv1_TMap(TMap(t,u)) == u);
axiom (forall t, u: Ty :: { TMap(t,u) } Tag(TMap(t,u)) == TagMap);

function TIMap(Ty, Ty) : Ty;
axiom (forall t, u: Ty :: { TIMap(t,u) } Inv0_TIMap(TIMap(t,u)) == t);
axiom (forall t, u: Ty :: { TIMap(t,u) } Inv1_TIMap(TIMap(t,u)) == u);
axiom (forall t, u: Ty :: { TIMap(t,u) } Tag(TIMap(t,u)) == TagIMap);


function Inv0_TBitvector(Ty) : int;
function Inv0_TSet(Ty) : Ty;
function Inv0_TISet(Ty) : Ty;
function Inv0_TSeq(Ty) : Ty;
function Inv0_TMultiSet(Ty) : Ty;
function Inv0_TMap(Ty) : Ty;
function Inv1_TMap(Ty) : Ty;
function Inv0_TIMap(Ty) : Ty;
function Inv1_TIMap(Ty) : Ty;

// -- Classes and Datatypes --

// -- Type Tags --
type TyTag;
function Tag(Ty) : TyTag;

const unique TagBool     : TyTag;
const unique TagChar     : TyTag;
const unique TagInt      : TyTag;
const unique TagReal     : TyTag;
const unique TagORDINAL  : TyTag;
const unique TagSet      : TyTag;
const unique TagISet     : TyTag;
const unique TagMultiSet : TyTag;
const unique TagSeq      : TyTag;
const unique TagMap      : TyTag;
const unique TagIMap     : TyTag;
const unique TagClass    : TyTag;

type TyTagFamily;
function TagFamily(Ty): TyTagFamily;

// ---------------------------------------------------------------
// -- Literals ---------------------------------------------------
// ---------------------------------------------------------------
function {:identity} Lit<T>(x: T): T { x }
axiom (forall<T> x: T :: { $Box(Lit(x)) } $Box(Lit(x)) == Lit($Box(x)) );

// Specialize Lit to concrete types.
// These aren't logically required, but on some examples improve
// verification speed
function {:identity} LitInt(x: int): int { x }
axiom (forall x: int :: { $Box(LitInt(x)) } $Box(LitInt(x)) == Lit($Box(x)) );

function {:identity} LitReal(x: real): real { x }
axiom (forall x: real :: { $Box(LitReal(x)) } $Box(LitReal(x)) == Lit($Box(x)) );

// ---------------------------------------------------------------
// -- Characters -------------------------------------------------
// ---------------------------------------------------------------

#if UNICODE_CHAR
function {:inline} char#IsChar(n: int): bool {
  (0                  <= n && n < 55296   /* 0xD800 */) ||
  (57344 /* 0xE000 */ <= n && n < 1114112 /* 0x11_0000 */ )
}
#else
function {:inline} char#IsChar(n: int): bool {
  0 <= n && n < 65536
}
#endif

type char;
function char#FromInt(int): char;
axiom (forall n: int ::
  { char#FromInt(n) }
  char#IsChar(n) ==> char#ToInt(char#FromInt(n)) == n);

function char#ToInt(char): int;
axiom (forall ch: char ::
  { char#ToInt(ch) }
  char#FromInt(char#ToInt(ch)) == ch &&
  char#IsChar(char#ToInt(ch)));

function char#Plus(char, char): char;
axiom (forall a: char, b: char ::
  { char#Plus(a, b) }
  char#Plus(a, b) == char#FromInt(char#ToInt(a) + char#ToInt(b)));

function char#Minus(char, char): char;
axiom (forall a: char, b: char ::
  { char#Minus(a, b) }
  char#Minus(a, b) == char#FromInt(char#ToInt(a) - char#ToInt(b)));

// ---------------------------------------------------------------
// -- References -------------------------------------------------
// ---------------------------------------------------------------

type ref;
const null: ref;

// ---------------------------------------------------------------
// -- Boxing and unboxing ----------------------------------------
// ---------------------------------------------------------------

type Box;
const $ArbitraryBoxValue: Box;

function $Box<T>(T): Box;
function $Unbox<T>(Box): T;
axiom (forall<T> x : T   :: { $Box(x) } {:weight 3} $Unbox($Box(x)) == x);
axiom (forall<T> x : Box :: { $Unbox(x): T}      $Box($Unbox(x): T) == x);


// Corresponding entries for boxes...
// This could probably be solved by having Box also inhabit Ty
function $IsBox(Box,Ty): bool;
function $IsAllocBox(Box,Ty,Heap): bool;

axiom (forall bx : Box ::
    { $IsBox(bx, TInt) }
    ( $IsBox(bx, TInt) ==> $Box($Unbox(bx) : int) == bx && $Is($Unbox(bx) : int, TInt)));
axiom (forall bx : Box ::
    { $IsBox(bx, TReal) }
    ( $IsBox(bx, TReal) ==> $Box($Unbox(bx) : real) == bx && $Is($Unbox(bx) : real, TReal)));
axiom (forall bx : Box ::
    { $IsBox(bx, TBool) }
    ( $IsBox(bx, TBool) ==> $Box($Unbox(bx) : bool) == bx && $Is($Unbox(bx) : bool, TBool)));
axiom (forall bx : Box ::
    { $IsBox(bx, TChar) }
    ( $IsBox(bx, TChar) ==> $Box($Unbox(bx) : char) == bx && $Is($Unbox(bx) : char, TChar)));

// Since each bitvector type is a separate type in Boogie, the Box/Unbox axioms for bitvectors are
// generated programmatically. Except, Bv0 is given here.
axiom (forall bx : Box ::
    { $IsBox(bx, TBitvector(0)) }
    ( $IsBox(bx, TBitvector(0)) ==> $Box($Unbox(bx) : Bv0) == bx && $Is($Unbox(bx) : Bv0, TBitvector(0))));

axiom (forall bx : Box, t : Ty ::
    { $IsBox(bx, TSet(t)) }
    ( $IsBox(bx, TSet(t)) ==> $Box($Unbox(bx) : Set) == bx && $Is($Unbox(bx) : Set, TSet(t))));
axiom (forall bx : Box, t : Ty ::
    { $IsBox(bx, TISet(t)) }
    ( $IsBox(bx, TISet(t)) ==> $Box($Unbox(bx) : ISet) == bx && $Is($Unbox(bx) : ISet, TISet(t))));
axiom (forall bx : Box, t : Ty ::
    { $IsBox(bx, TMultiSet(t)) }
    ( $IsBox(bx, TMultiSet(t)) ==> $Box($Unbox(bx) : MultiSet) == bx && $Is($Unbox(bx) : MultiSet, TMultiSet(t))));
axiom (forall bx : Box, t : Ty ::
    { $IsBox(bx, TSeq(t)) }
    ( $IsBox(bx, TSeq(t)) ==> $Box($Unbox(bx) : Seq) == bx && $Is($Unbox(bx) : Seq, TSeq(t))));
axiom (forall bx : Box, s : Ty, t : Ty ::
    { $IsBox(bx, TMap(s, t)) }
    ( $IsBox(bx, TMap(s, t)) ==> $Box($Unbox(bx) : Map) == bx && $Is($Unbox(bx) : Map, TMap(s, t))));
axiom (forall bx : Box, s : Ty, t : Ty ::
    { $IsBox(bx, TIMap(s, t)) }
    ( $IsBox(bx, TIMap(s, t)) ==> $Box($Unbox(bx) : IMap) == bx && $Is($Unbox(bx) : IMap, TIMap(s, t))));

axiom (forall<T> v : T, t : Ty ::
    { $IsBox($Box(v), t) }
    ( $IsBox($Box(v), t) <==> $Is(v,t) ));
axiom (forall<T> v : T, t : Ty, h : Heap ::
    { $IsAllocBox($Box(v), t, h) }
    ( $IsAllocBox($Box(v), t, h) <==> $IsAlloc(v,t,h) ));

// ---------------------------------------------------------------
// -- Is and IsAlloc ---------------------------------------------
// ---------------------------------------------------------------

// Type-argument to $Is is the /representation type/,
// the second value argument to $Is is the actual type.
function $Is<T>(T,Ty): bool;           // no heap for now
axiom(forall v : int  :: { $Is(v,TInt) }  $Is(v,TInt));
axiom(forall v : real :: { $Is(v,TReal) } $Is(v,TReal));
axiom(forall v : bool :: { $Is(v,TBool) } $Is(v,TBool));
axiom(forall v : char :: { $Is(v,TChar) } $Is(v,TChar));
axiom(forall v : ORDINAL :: { $Is(v,TORDINAL) } $Is(v,TORDINAL));

// Since every bitvector type is a separate type in Boogie, the $Is/$IsAlloc axioms
// for bitvectors are generated programatically. Except, TBitvector(0) is given here.
axiom (forall v: Bv0 :: { $Is(v, TBitvector(0)) } $Is(v, TBitvector(0)));

axiom (forall v: Set, t0: Ty :: { $Is(v, TSet(t0)) }
  $Is(v, TSet(t0)) <==>
  (forall bx: Box :: { Set#IsMember(v, bx) }
    Set#IsMember(v, bx) ==> $IsBox(bx, t0)));
axiom (forall v: ISet, t0: Ty :: { $Is(v, TISet(t0)) }
  $Is(v, TISet(t0)) <==>
  (forall bx: Box :: { v[bx] }
    v[bx] ==> $IsBox(bx, t0)));
axiom (forall v: MultiSet, t0: Ty :: { $Is(v, TMultiSet(t0)) }
  $Is(v, TMultiSet(t0)) <==>
  (forall bx: Box :: { MultiSet#Multiplicity(v, bx) }
    0 < MultiSet#Multiplicity(v, bx) ==> $IsBox(bx, t0)));
axiom (forall v: MultiSet, t0: Ty :: { $Is(v, TMultiSet(t0)) }
  $Is(v, TMultiSet(t0)) ==> $IsGoodMultiSet(v));
axiom (forall v: Seq, t0: Ty :: { $Is(v, TSeq(t0)) }
  $Is(v, TSeq(t0)) <==>
  (forall i : int :: { Seq#Index(v, i) }
    0 <= i && i < Seq#Length(v) ==>
    $IsBox(Seq#Index(v, i), t0)));

axiom (forall v: Map, t0: Ty, t1: Ty ::
  { $Is(v, TMap(t0, t1)) }
  $Is(v, TMap(t0, t1))
     <==> (forall bx: Box ::
      { Map#Elements(v)[bx] } { Set#IsMember(Map#Domain(v), bx) }
      Set#IsMember(Map#Domain(v), bx) ==>
        $IsBox(Map#Elements(v)[bx], t1) &&
        $IsBox(bx, t0)));

axiom (forall v: Map, t0: Ty, t1: Ty ::
  { $Is(v, TMap(t0, t1)) }
  $Is(v, TMap(t0, t1)) ==>
    $Is(Map#Domain(v), TSet(t0)) &&
    $Is(Map#Values(v), TSet(t1)) &&
    $Is(Map#Items(v), TSet(Tclass._System.Tuple2(t0, t1))));
axiom (forall v: IMap, t0: Ty, t1: Ty ::
  { $Is(v, TIMap(t0, t1)) }
  $Is(v, TIMap(t0, t1))
     <==> (forall bx: Box ::
      { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] }
      IMap#Domain(v)[bx] ==>
        $IsBox(IMap#Elements(v)[bx], t1) &&
        $IsBox(bx, t0)));
axiom (forall v: IMap, t0: Ty, t1: Ty ::
  { $Is(v, TIMap(t0, t1)) }
  $Is(v, TIMap(t0, t1)) ==>
    $Is(IMap#Domain(v), TISet(t0)) &&
    $Is(IMap#Values(v), TISet(t1)) &&
    $Is(IMap#Items(v), TISet(Tclass._System.Tuple2(t0, t1))));

function $IsAlloc<T>(T,Ty,Heap): bool;
axiom(forall h : Heap, v : int  :: { $IsAlloc(v,TInt,h) }  $IsAlloc(v,TInt,h));
axiom(forall h : Heap, v : real :: { $IsAlloc(v,TReal,h) } $IsAlloc(v,TReal,h));
axiom(forall h : Heap, v : bool :: { $IsAlloc(v,TBool,h) } $IsAlloc(v,TBool,h));
axiom(forall h : Heap, v : char :: { $IsAlloc(v,TChar,h) } $IsAlloc(v,TChar,h));
axiom(forall h : Heap, v : ORDINAL :: { $IsAlloc(v,TORDINAL,h) } $IsAlloc(v,TORDINAL,h));

axiom (forall v: Bv0, h: Heap :: { $IsAlloc(v, TBitvector(0), h) } $IsAlloc(v, TBitvector(0), h));

axiom (forall v: Set, t0: Ty, h: Heap :: { $IsAlloc(v, TSet(t0), h) }
  $IsAlloc(v, TSet(t0), h) <==>
  (forall bx: Box :: { Set#IsMember(v, bx) }
    Set#IsMember(v, bx) ==> $IsAllocBox(bx, t0, h)));
axiom (forall v: ISet, t0: Ty, h: Heap :: { $IsAlloc(v, TISet(t0), h) }
  $IsAlloc(v, TISet(t0), h) <==>
  (forall bx: Box :: { v[bx] }
    v[bx] ==> $IsAllocBox(bx, t0, h)));
axiom (forall v: MultiSet, t0: Ty, h: Heap :: { $IsAlloc(v, TMultiSet(t0), h) }
  $IsAlloc(v, TMultiSet(t0), h) <==>
  (forall bx: Box :: { MultiSet#Multiplicity(v, bx) }
    0 < MultiSet#Multiplicity(v, bx) ==> $IsAllocBox(bx, t0, h)));
axiom (forall v: Seq, t0: Ty, h: Heap :: { $IsAlloc(v, TSeq(t0), h) }
  $IsAlloc(v, TSeq(t0), h) <==>
  (forall i : int :: { Seq#Index(v, i) }
    0 <= i && i < Seq#Length(v) ==>
	$IsAllocBox(Seq#Index(v, i), t0, h)));
	
axiom (forall v: Map, t0: Ty, t1: Ty, h: Heap ::
  { $IsAlloc(v, TMap(t0, t1), h) }
  $IsAlloc(v, TMap(t0, t1), h)
     <==> (forall bx: Box ::
      { Map#Elements(v)[bx] } { Set#IsMember(Map#Domain(v), bx) }
      Set#IsMember(Map#Domain(v), bx) ==>
        $IsAllocBox(Map#Elements(v)[bx], t1, h) &&
        $IsAllocBox(bx, t0, h)));

axiom (forall v: IMap, t0: Ty, t1: Ty, h: Heap ::
  { $IsAlloc(v, TIMap(t0, t1), h) }
  $IsAlloc(v, TIMap(t0, t1), h)
     <==> (forall bx: Box ::
      { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] }
      IMap#Domain(v)[bx] ==>
        $IsAllocBox(IMap#Elements(v)[bx], t1, h) &&
        $IsAllocBox(bx, t0, h)));


function $AlwaysAllocated(Ty): bool;
  axiom (forall ty: Ty :: { $AlwaysAllocated(ty) }
    $AlwaysAllocated(ty) ==>
    (forall h: Heap, v: Box  :: { $IsAllocBox(v, ty, h) }  $IsBox(v, ty) ==> $IsAllocBox(v, ty, h)));

function $OlderTag(Heap): bool;

// ---------------------------------------------------------------
// -- Encoding of type names -------------------------------------
// ---------------------------------------------------------------

type ClassName;
const unique class._System.int: ClassName;
const unique class._System.bool: ClassName;
const unique class._System.set: ClassName;
const unique class._System.seq: ClassName;
const unique class._System.multiset: ClassName;

function Tclass._System.object?(): Ty;
function Tclass._System.Tuple2(Ty, Ty): Ty;

function /*{:never_pattern true}*/ dtype(ref): Ty; // changed from ClassName to Ty

function TypeTuple(a: ClassName, b: ClassName): ClassName;
function TypeTupleCar(ClassName): ClassName;
function TypeTupleCdr(ClassName): ClassName;
// TypeTuple is injective in both arguments:
axiom (forall a: ClassName, b: ClassName :: { TypeTuple(a,b) }
  TypeTupleCar(TypeTuple(a,b)) == a &&
  TypeTupleCdr(TypeTuple(a,b)) == b);

// -- Function handles -------------------------------------------

type HandleType;

function SetRef_to_SetBox(s: [ref]bool): Set;
axiom (forall s: [ref]bool, bx: Box :: { Set#IsMember(SetRef_to_SetBox(s), bx) }
  Set#IsMember(SetRef_to_SetBox(s), bx) == s[$Unbox(bx): ref]);
axiom (forall s: [ref]bool :: { SetRef_to_SetBox(s) }
  $Is(SetRef_to_SetBox(s), TSet(Tclass._System.object?())));

// Functions ApplyN, RequiresN, and ReadsN are generated on demand by the translator,
// but Apply1 is referred to in the prelude, so its definition is hardcoded here.
function Apply1(Ty, Ty, Heap, HandleType, Box): Box;

// ---------------------------------------------------------------
// -- Datatypes --------------------------------------------------
// ---------------------------------------------------------------

type DatatypeType;

type DtCtorId;
function DatatypeCtorId(DatatypeType): DtCtorId;

function DtRank(DatatypeType): int;
function BoxRank(Box): int;

axiom (forall d: DatatypeType :: {BoxRank($Box(d))} BoxRank($Box(d)) == DtRank(d));

// ---------------------------------------------------------------
// -- Big Ordinals -----------------------------------------------
// ---------------------------------------------------------------

type ORDINAL = Box;  // :| There are more big ordinals than boxes

// The following two functions give an abstracton over all ordinals.
// Function ORD#IsNat returns true when the ordinal is one of the natural
// numbers.  Function ORD#Offset gives how many successors (that is,
// +1 operations) an ordinal is above the nearest lower limit ordinal.
// That is, if the ordinal is \lambda+n, then ORD#Offset returns n.
function ORD#IsNat(ORDINAL): bool;
function ORD#Offset(ORDINAL): int;
axiom (forall o:ORDINAL :: { ORD#Offset(o) } 0 <= ORD#Offset(o));

function {:inline} ORD#IsLimit(o: ORDINAL): bool { ORD#Offset(o) == 0 }
function {:inline} ORD#IsSucc(o: ORDINAL): bool { 0 < ORD#Offset(o) }

function ORD#FromNat(int): ORDINAL;
axiom (forall n:int :: { ORD#FromNat(n) }
  0 <= n ==> ORD#IsNat(ORD#FromNat(n)) && ORD#Offset(ORD#FromNat(n)) == n);
axiom (forall o:ORDINAL :: { ORD#Offset(o) } { ORD#IsNat(o) }
  ORD#IsNat(o) ==> o == ORD#FromNat(ORD#Offset(o)));

function ORD#Less(ORDINAL, ORDINAL): bool;
axiom (forall o,p: ORDINAL :: { ORD#Less(o,p) }
  (ORD#Less(o,p) ==> o != p) &&  // irreflexivity
  (ORD#IsNat(o) && !ORD#IsNat(p) ==> ORD#Less(o,p)) &&
  (ORD#IsNat(o) && ORD#IsNat(p) ==> ORD#Less(o,p) == (ORD#Offset(o) < ORD#Offset(p))) &&
  (ORD#Less(o,p) && ORD#IsNat(p) ==> ORD#IsNat(o)));
// ORD#Less is trichotomous:
axiom (forall o,p: ORDINAL :: { ORD#Less(o,p), ORD#Less(p,o) }
  ORD#Less(o,p) || o == p || ORD#Less(p,o));
// ORD#Less is transitive:
axiom (forall o,p,r: ORDINAL ::
  { ORD#Less(o,p), ORD#Less(p,r) }
  { ORD#Less(o,p), ORD#Less(o,r) }
  ORD#Less(o,p) && ORD#Less(p,r) ==> ORD#Less(o,r));

// ORD#LessThanLimit is a synonym of ORD#Less, introduced for more selected triggering
function ORD#LessThanLimit(ORDINAL, ORDINAL): bool;
axiom (forall o,p: ORDINAL :: { ORD#LessThanLimit(o, p) }
  ORD#LessThanLimit(o, p) == ORD#Less(o, p));

function ORD#Plus(ORDINAL, ORDINAL): ORDINAL;
axiom (forall o,p: ORDINAL :: { ORD#Plus(o,p) }
  (ORD#IsNat(ORD#Plus(o,p)) ==> ORD#IsNat(o) && ORD#IsNat(p)) &&
  (ORD#IsNat(p) ==>
    ORD#IsNat(ORD#Plus(o,p)) == ORD#IsNat(o) &&
    ORD#Offset(ORD#Plus(o,p)) == ORD#Offset(o) + ORD#Offset(p)));
axiom (forall o,p: ORDINAL :: { ORD#Plus(o,p) }
  (o == ORD#Plus(o, p) || ORD#Less(o, ORD#Plus(o, p))) &&
  (p == ORD#Plus(o, p) || ORD#Less(p, ORD#Plus(o, p))));
axiom (forall o,p: ORDINAL :: { ORD#Plus(o,p) }
  (o == ORD#FromNat(0) ==> ORD#Plus(o, p) == p) &&
  (p == ORD#FromNat(0) ==> ORD#Plus(o, p) == o));

function ORD#Minus(ORDINAL, ORDINAL): ORDINAL;
axiom (forall o,p: ORDINAL :: { ORD#Minus(o,p) }
  ORD#IsNat(p) && ORD#Offset(p) <= ORD#Offset(o) ==>
    ORD#IsNat(ORD#Minus(o,p)) == ORD#IsNat(o) &&
    ORD#Offset(ORD#Minus(o,p)) == ORD#Offset(o) - ORD#Offset(p));
axiom (forall o,p: ORDINAL :: { ORD#Minus(o,p) }
  ORD#IsNat(p) && ORD#Offset(p) <= ORD#Offset(o) ==>
    (p == ORD#FromNat(0) && ORD#Minus(o, p) == o) ||
    (p != ORD#FromNat(0) && ORD#Less(ORD#Minus(o, p), o)));

// o+m+n == o+(m+n)
axiom (forall o: ORDINAL, m,n: int ::
  { ORD#Plus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) }
  0 <= m && 0 <= n ==>
  ORD#Plus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) == ORD#Plus(o, ORD#FromNat(m+n)));
// o-m-n == o-(m+n)
axiom (forall o: ORDINAL, m,n: int ::
  { ORD#Minus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) }
  0 <= m && 0 <= n && m+n <= ORD#Offset(o) ==>
  ORD#Minus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) == ORD#Minus(o, ORD#FromNat(m+n)));
// o+m-n == EITHER o+(m-n) OR o-(n-m)
axiom (forall o: ORDINAL, m,n: int ::
  { ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) }
  0 <= m && 0 <= n && n <= ORD#Offset(o) + m ==>
    (0 <= m - n ==> ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) == ORD#Plus(o, ORD#FromNat(m-n))) &&
    (m - n <= 0 ==> ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) == ORD#Minus(o, ORD#FromNat(n-m))));
// o-m+n == EITHER o-(m-n) OR o+(n-m)
axiom (forall o: ORDINAL, m,n: int ::
  { ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) }
  0 <= m && 0 <= n && n <= ORD#Offset(o) + m ==>
    (0 <= m - n ==> ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) == ORD#Minus(o, ORD#FromNat(m-n))) &&
    (m - n <= 0 ==> ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) == ORD#Plus(o, ORD#FromNat(n-m))));

// ---------------------------------------------------------------
// -- Layers of function encodings -------------------------------
// ---------------------------------------------------------------

type LayerType;
const $LZ: LayerType;
function $LS(LayerType): LayerType;
function AsFuelBottom(LayerType) : LayerType;

function AtLayer<A>([LayerType]A, LayerType): A;
axiom (forall<A> f : [LayerType]A, ly : LayerType :: { AtLayer(f,ly) } AtLayer(f,ly) == f[ly]);
axiom (forall<A> f : [LayerType]A, ly : LayerType :: { AtLayer(f,$LS(ly)) } AtLayer(f,$LS(ly)) == AtLayer(f,ly));

// ---------------------------------------------------------------
// -- Fields -----------------------------------------------------
// ---------------------------------------------------------------

type Field;

function FDim(Field): int uses {
  axiom FDim(alloc) == 0;
}

function IndexField(int): Field;
axiom (forall i: int :: { IndexField(i) } FDim(IndexField(i)) == 1);
function IndexField_Inverse(Field): int;
axiom (forall i: int :: { IndexField(i) } IndexField_Inverse(IndexField(i)) == i);

function MultiIndexField(Field, int): Field;
axiom (forall f: Field, i: int :: { MultiIndexField(f,i) } FDim(MultiIndexField(f,i)) == FDim(f) + 1);
function MultiIndexField_Inverse0(Field): Field;
function MultiIndexField_Inverse1(Field): int;
axiom (forall f: Field, i: int :: { MultiIndexField(f,i) }
  MultiIndexField_Inverse0(MultiIndexField(f,i)) == f &&
  MultiIndexField_Inverse1(MultiIndexField(f,i)) == i);

function DeclType(Field): ClassName;

type NameFamily;
function DeclName(Field): NameFamily uses {
  axiom DeclName(alloc) == allocName;
}
function FieldOfDecl(ClassName, NameFamily): Field;
axiom (forall cl : ClassName, nm: NameFamily ::
   {FieldOfDecl(cl, nm): Field}
   DeclType(FieldOfDecl(cl, nm): Field) == cl && DeclName(FieldOfDecl(cl, nm): Field) == nm);

function $IsGhostField(Field): bool uses {
   axiom $IsGhostField(alloc); // treat as ghost field, since it is allowed to be changed by ghost code
}
axiom (forall h: Heap, k: Heap :: { $HeapSuccGhost(h,k) }
  $HeapSuccGhost(h,k) ==>
    $HeapSucc(h,k) &&
    (forall o: ref, f: Field :: { read(k, o, f) }
      !$IsGhostField(f) ==> read(h, o, f) == read(k, o, f)));

// ---------------------------------------------------------------
// -- Allocatedness and Heap Succession --------------------------
// ---------------------------------------------------------------


// $IsAlloc and $IsAllocBox are monotonic

axiom (forall<T> h, k : Heap, v : T, t : Ty ::
  { $HeapSucc(h, k), $IsAlloc(v, t, h) }
  $HeapSucc(h, k) ==> $IsAlloc(v, t, h) ==> $IsAlloc(v, t, k));
axiom (forall h, k : Heap, bx : Box, t : Ty ::
  { $HeapSucc(h, k), $IsAllocBox(bx, t, h) }
  $HeapSucc(h, k) ==> $IsAllocBox(bx, t, h) ==> $IsAllocBox(bx, t, k));

// No axioms for $Is and $IsBox since they don't talk about the heap.

const unique alloc: Field;
const unique allocName: NameFamily;

// ---------------------------------------------------------------
// -- Arrays -----------------------------------------------------
// ---------------------------------------------------------------

function _System.array.Length(a: ref): int;
axiom (forall o: ref :: {_System.array.Length(o)} 0 <= _System.array.Length(o));


// ---------------------------------------------------------------
// -- Reals ------------------------------------------------------
// ---------------------------------------------------------------

function Int(x: real): int { int(x) }
function Real(x: int): real { real(x) }
axiom (forall i: int :: { Int(Real(i)) } Int(Real(i)) == i);

function {:inline} _System.real.Floor(x: real): int { Int(x) }

// ---------------------------------------------------------------
// -- The heap ---------------------------------------------------
// ---------------------------------------------------------------
type Heap = [ref][Field]Box;
function {:inline} read(H: Heap, r: ref, f: Field) : Box { H[r][f] }
function {:inline} update(H:Heap, r:ref, f: Field, v: Box) : Heap { H[r := H[r][f := v]] }

function $IsGoodHeap(Heap): bool;
function $IsHeapAnchor(Heap): bool;
var $Heap: Heap where $IsGoodHeap($Heap) && $IsHeapAnchor($Heap);

// The following is used as a reference heap in places where the translation needs a heap
// but the expression generated is really one that is (at least in a correct program)
// independent of the heap.
const $OneHeap: Heap uses {
  axiom $IsGoodHeap($OneHeap);
}

function $HeapSucc(Heap, Heap): bool;
axiom (forall h: Heap, r: ref, f: Field, x: Box :: { update(h, r, f, x) }
  $IsGoodHeap(update(h, r, f, x)) ==>
  $HeapSucc(h, update(h, r, f, x)));
axiom (forall a,b,c: Heap :: { $HeapSucc(a,b), $HeapSucc(b,c) }
  a != c ==> $HeapSucc(a,b) && $HeapSucc(b,c) ==> $HeapSucc(a,c));
axiom (forall h: Heap, k: Heap :: { $HeapSucc(h,k) }
  $HeapSucc(h,k) ==> (forall o: ref :: { read(k, o, alloc) } $Unbox(read(h, o, alloc)) ==> $Unbox(read(k, o, alloc))));

function $HeapSuccGhost(Heap, Heap): bool;

// ---------------------------------------------------------------
// -- Useful macros ----------------------------------------------
// ---------------------------------------------------------------

// havoc everything in $Heap, except {this}+rds+nw
procedure $YieldHavoc(this: ref, rds: Set, nw: Set);
  modifies $Heap;
  ensures (forall $o: ref, $f: Field :: { read($Heap, $o, $f) }
            $o != null && $Unbox(read(old($Heap), $o, alloc)) ==>
            $o == this || Set#IsMember(rds, $Box($o)) || Set#IsMember(nw, $Box($o)) ==>
              read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);

// havoc everything in $Heap, except rds-modi-{this}
procedure $IterHavoc0(this: ref, rds: Set, modi: Set);
  modifies $Heap;
  ensures (forall $o: ref, $f: Field :: { read($Heap, $o, $f) }
            $o != null && $Unbox(read(old($Heap), $o, alloc)) ==>
            Set#IsMember(rds, $Box($o)) && !Set#IsMember(modi, $Box($o)) && $o != this ==>
              read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);

// havoc $Heap at {this}+modi+nw
procedure $IterHavoc1(this: ref, modi: Set, nw: Set);
  modifies $Heap;
  ensures (forall $o: ref, $f: Field :: { read($Heap, $o, $f) }
            $o != null && $Unbox(read(old($Heap), $o, alloc)) ==>
              read($Heap, $o, $f) == read(old($Heap), $o, $f) ||
              $o == this || Set#IsMember(modi, $Box($o)) || Set#IsMember(nw, $Box($o)));
  ensures $HeapSucc(old($Heap), $Heap);

procedure $IterCollectNewObjects(prevHeap: Heap, newHeap: Heap, this: ref, NW: Field)
                        returns (s: Set);
  ensures (forall bx: Box :: { Set#IsMember(s, bx) } Set#IsMember(s, bx) <==>
              Set#IsMember($Unbox(read(newHeap, this, NW)) : Set, bx) ||
              ($Unbox(bx) != null && !$Unbox(read(prevHeap, $Unbox(bx):ref, alloc)) && $Unbox(read(newHeap, $Unbox(bx):ref, alloc))));

// ---------------------------------------------------------------
// -- Axiomatizations --------------------------------------------
// ---------------------------------------------------------------

// ---------------------------------------------------------------
// -- Axiomatization of sets -------------------------------------
// ---------------------------------------------------------------

#include "Sets.bpl"

// FIXME: Finite-set comprehensions are translated into Boogie lambda expressions for Boogie maps and then converted,
// using function Set#FromBoogieMap, to a set. The use of Boogie lambda expressions is convenient, since Boogie
// performs lambda lifting on them. However, this is NOT right, because it allows ANY lambda to be converted
// into a finite set. This should be fixed by doing the lambda lifting directly in Dafny and not use Boogie lambda
// expressions.
function Set#FromBoogieMap([Box]bool): Set;
axiom (forall m: [Box]bool, bx: Box ::
  { Set#IsMember(Set#FromBoogieMap(m), bx) }
  Set#IsMember(Set#FromBoogieMap(m), bx) == m[bx]);

// ---------------------------------------------------------------
// -- Axiomatization of isets -------------------------------------
// ---------------------------------------------------------------

type ISet = [Box]bool;

function ISet#Empty(): ISet;
axiom (forall o: Box :: { ISet#Empty()[o] } !ISet#Empty()[o]);

function ISet#FromSet(Set): ISet;
axiom (forall s: Set, bx: Box ::
  { ISet#FromSet(s)[bx] }
  ISet#FromSet(s)[bx] == Set#IsMember(s, bx));

function ISet#UnionOne(ISet, Box): ISet;
axiom (forall a: ISet, x: Box, o: Box :: { ISet#UnionOne(a,x)[o] }
  ISet#UnionOne(a,x)[o] <==> o == x || a[o]);
axiom (forall a: ISet, x: Box :: { ISet#UnionOne(a, x) }
  ISet#UnionOne(a, x)[x]);
axiom (forall a: ISet, x: Box, y: Box :: { ISet#UnionOne(a, x), a[y] }
  a[y] ==> ISet#UnionOne(a, x)[y]);

function ISet#Union(ISet, ISet): ISet;
axiom (forall a: ISet, b: ISet, o: Box :: { ISet#Union(a,b)[o] }
  ISet#Union(a,b)[o] <==> a[o] || b[o]);
axiom (forall a, b: ISet, y: Box :: { ISet#Union(a, b), a[y] }
  a[y] ==> ISet#Union(a, b)[y]);
axiom (forall a, b: ISet, y: Box :: { ISet#Union(a, b), b[y] }
  b[y] ==> ISet#Union(a, b)[y]);
axiom (forall a, b: ISet :: { ISet#Union(a, b) }
  ISet#Disjoint(a, b) ==>
    ISet#Difference(ISet#Union(a, b), a) == b &&
    ISet#Difference(ISet#Union(a, b), b) == a);

function ISet#Intersection(ISet, ISet): ISet;
axiom (forall a: ISet, b: ISet, o: Box :: { ISet#Intersection(a,b)[o] }
  ISet#Intersection(a,b)[o] <==> a[o] && b[o]);

axiom (forall a, b: ISet :: { ISet#Union(ISet#Union(a, b), b) }
  ISet#Union(ISet#Union(a, b), b) == ISet#Union(a, b));
axiom (forall a, b: ISet :: { ISet#Union(a, ISet#Union(a, b)) }
  ISet#Union(a, ISet#Union(a, b)) == ISet#Union(a, b));
axiom (forall a, b: ISet :: { ISet#Intersection(ISet#Intersection(a, b), b) }
  ISet#Intersection(ISet#Intersection(a, b), b) == ISet#Intersection(a, b));
axiom (forall a, b: ISet :: { ISet#Intersection(a, ISet#Intersection(a, b)) }
  ISet#Intersection(a, ISet#Intersection(a, b)) == ISet#Intersection(a, b));


function ISet#Difference(ISet, ISet): ISet;
axiom (forall a: ISet, b: ISet, o: Box :: { ISet#Difference(a,b)[o] }
  ISet#Difference(a,b)[o] <==> a[o] && !b[o]);
axiom (forall a, b: ISet, y: Box :: { ISet#Difference(a, b), b[y] }
  b[y] ==> !ISet#Difference(a, b)[y] );

function ISet#Subset(ISet, ISet): bool;
axiom (forall a: ISet, b: ISet :: { ISet#Subset(a,b) }
  ISet#Subset(a,b) <==> (forall o: Box :: {a[o]} {b[o]} a[o] ==> b[o]));

function ISet#Equal(ISet, ISet): bool;
axiom (forall a: ISet, b: ISet :: { ISet#Equal(a,b) }
  ISet#Equal(a,b) <==> (forall o: Box :: {a[o]} {b[o]} a[o] <==> b[o]));
axiom (forall a: ISet, b: ISet :: { ISet#Equal(a,b) }  // extensionality axiom for sets
  ISet#Equal(a,b) ==> a == b);

function ISet#Disjoint(ISet, ISet): bool;
axiom (forall a: ISet, b: ISet :: { ISet#Disjoint(a,b) }
  ISet#Disjoint(a,b) <==> (forall o: Box :: {a[o]} {b[o]} !a[o] || !b[o]));

// ---------------------------------------------------------------
// -- Axiomatization of multisets --------------------------------
// ---------------------------------------------------------------

#include "Math.bpl"

#include "Multisets.bpl"

// ---------------------------------------------------------------
// -- Axiomatization of sequences --------------------------------
// ---------------------------------------------------------------

#include "Sequences.bpl"

// The empty sequence $Is any type
//axiom (forall t: Ty :: {$Is(Seq#Empty(): Seq, TSeq(t))} $Is(Seq#Empty(): Seq, TSeq(t)));

// Build preserves $Is
axiom (forall s: Seq, bx: Box, t: Ty :: { $Is(Seq#Build(s, bx), TSeq(t)) }
    $Is(s, TSeq(t)) && $IsBox(bx, t) ==> $Is(Seq#Build(s, bx), TSeq(t)));

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
        n0 + 1 == n1 && 0 <= n0 && n1 <= _System.array.Length(a) ==> Seq#Take(Seq#FromArray(h, a), n1) == Seq#Build(Seq#Take(Seq#FromArray(h, a), n0), read(h, a, IndexField(n0): Field)) );

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

// ---------------------------------------------------------------
// -- Axiomatization of Maps -------------------------------------
// ---------------------------------------------------------------

type Map;

// A Map is defined by three functions, Map#Domain, Map#Elements, and #Map#Card.

function Map#Domain(Map) : Set;

function Map#Elements(Map) : [Box]Box;

function Map#Card(Map) : int;

axiom (forall m: Map :: { Map#Card(m) } 0 <= Map#Card(m));

axiom (forall m: Map ::
  { Map#Card(m) }
  Map#Card(m) == 0 <==> m == Map#Empty());

axiom (forall m: Map ::
  { Map#Domain(m) }
  m == Map#Empty() || (exists k: Box :: Set#IsMember(Map#Domain(m), k)));
axiom (forall m: Map ::
  { Map#Values(m) }
  m == Map#Empty() || (exists v: Box :: Set#IsMember(Map#Values(m), v)));
axiom (forall m: Map ::
  { Map#Items(m) }
  m == Map#Empty() || (exists k, v: Box :: Set#IsMember(Map#Items(m), $Box(#_System._tuple#2._#Make2(k, v)))));

axiom (forall m: Map ::
  { Set#Card(Map#Domain(m)) } { Map#Card(m) }
  Set#Card(Map#Domain(m)) == Map#Card(m));
axiom (forall m: Map ::
  { Set#Card(Map#Values(m)) } { Map#Card(m) }
  Set#Card(Map#Values(m)) <= Map#Card(m));
axiom (forall m: Map ::
  { Set#Card(Map#Items(m)) } { Map#Card(m) }
  Set#Card(Map#Items(m)) == Map#Card(m));

// The set of Values of a Map can be obtained by the function Map#Values, which is
// defined as follows.  Remember, a Set is defined by Set#IsMember and Map#Card, so
// we need to define what these mean for the Set returned by Map#Values.

function Map#Values(Map) : Set;

axiom (forall m: Map, v: Box :: { Set#IsMember(Map#Values(m), v) }
  Set#IsMember(Map#Values(m), v) ==
	(exists u: Box :: { Set#IsMember(Map#Domain(m), u) } { Map#Elements(m)[u] }
	  Set#IsMember(Map#Domain(m), u) &&
    v == Map#Elements(m)[u]));

// The set of Items--that is, (key,value) pairs--of a Map can be obtained by the
// function Map#Items.  Again, we need to define Set#IsMember and Set#Card for this
// set. Function Map#Items returns a set of pairs, and the axiomatization of pairs is Dafny specific.
// Therefore, the definition of Map#Items here is to be considered Dafny specific.  Also, note
// that it relies on the two destructors for 2-tuples.

function Map#Items(Map) : Set;

function #_System._tuple#2._#Make2(Box, Box) : DatatypeType;
function _System.Tuple2._0(DatatypeType) : Box;
function _System.Tuple2._1(DatatypeType) : Box;

axiom (forall m: Map, item: Box :: { Set#IsMember(Map#Items(m), item) }
  Set#IsMember(Map#Items(m), item) <==>
    Set#IsMember(Map#Domain(m), _System.Tuple2._0($Unbox(item))) &&
    Map#Elements(m)[_System.Tuple2._0($Unbox(item))] == _System.Tuple2._1($Unbox(item)));

// Here are the operations that produce Map values.

function Map#Empty(): Map;
axiom (forall u: Box ::
        { Set#IsMember(Map#Domain(Map#Empty(): Map), u) }
        !Set#IsMember(Map#Domain(Map#Empty(): Map), u));

function Map#Glue(Set, [Box]Box, Ty): Map;
axiom (forall a: Set, b: [Box]Box, t: Ty ::
  { Map#Domain(Map#Glue(a, b, t)) }
  Map#Domain(Map#Glue(a, b, t)) == a);
axiom (forall a: Set, b: [Box]Box, t: Ty ::
  { Map#Elements(Map#Glue(a, b, t)) }
  Map#Elements(Map#Glue(a, b, t)) == b);
axiom (forall a: Set, b: [Box]Box, t0, t1: Ty ::
  { Map#Glue(a, b, TMap(t0, t1)) }
  // In the following line, no trigger needed, since the quantifier only gets used in negative contexts
  (forall bx: Box :: Set#IsMember(a, bx) ==> $IsBox(bx, t0) && $IsBox(b[bx], t1))
  ==>
  $Is(Map#Glue(a, b, TMap(t0, t1)), TMap(t0, t1)));


//Build is used in displays, and for map updates
function Map#Build(Map, Box, Box): Map;
/*axiom (forall m: Map, u: Box, v: Box ::
  { Map#Domain(Map#Build(m, u, v))[u] } { Map#Elements(Map#Build(m, u, v))[u] }
  Map#Domain(Map#Build(m, u, v))[u] && Map#Elements(Map#Build(m, u, v))[u] == v);*/

axiom (forall m: Map, u: Box, u': Box, v: Box ::
  { Set#IsMember(Map#Domain(Map#Build(m, u, v)), u') } { Map#Elements(Map#Build(m, u, v))[u'] }
  (u' == u ==> Set#IsMember(Map#Domain(Map#Build(m, u, v)), u') &&
               Map#Elements(Map#Build(m, u, v))[u'] == v) &&
  (u' != u ==> Set#IsMember(Map#Domain(Map#Build(m, u, v)), u') == Set#IsMember(Map#Domain(m), u') &&
               Map#Elements(Map#Build(m, u, v))[u'] == Map#Elements(m)[u']));
axiom (forall m: Map, u: Box, v: Box :: { Map#Card(Map#Build(m, u, v)) }
  Set#IsMember(Map#Domain(m), u) ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m));
axiom (forall m: Map, u: Box, v: Box :: { Map#Card(Map#Build(m, u, v)) }
  !Set#IsMember(Map#Domain(m), u) ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m) + 1);

// Map operations
function Map#Merge(Map, Map): Map;
axiom (forall m: Map, n: Map ::
  { Map#Domain(Map#Merge(m, n)) }
  Map#Domain(Map#Merge(m, n)) == Set#Union(Map#Domain(m), Map#Domain(n)));
axiom (forall m: Map, n: Map, u: Box ::
  { Map#Elements(Map#Merge(m, n))[u] }
  Set#IsMember(Map#Domain(Map#Merge(m, n)), u) ==>
    (!Set#IsMember(Map#Domain(n), u) ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(m)[u]) &&
    (Set#IsMember(Map#Domain(n), u) ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(n)[u]));

function Map#Subtract(Map, Set): Map;
axiom (forall m: Map, s: Set ::
  { Map#Domain(Map#Subtract(m, s)) }
  Map#Domain(Map#Subtract(m, s)) == Set#Difference(Map#Domain(m), s));
axiom (forall m: Map, s: Set, u: Box ::
  { Map#Elements(Map#Subtract(m, s))[u] }
  Set#IsMember(Map#Domain(Map#Subtract(m, s)), u) ==>
    Map#Elements(Map#Subtract(m, s))[u] == Map#Elements(m)[u]);

//equality for maps
function Map#Equal(Map, Map): bool;
axiom (forall m: Map, m': Map::
  { Map#Equal(m, m') }
    Map#Equal(m, m') <==> (forall u : Box :: Set#IsMember(Map#Domain(m), u) == Set#IsMember(Map#Domain(m'), u)) &&
                          (forall u : Box :: Set#IsMember(Map#Domain(m), u) ==> Map#Elements(m)[u] == Map#Elements(m')[u]));
// extensionality
axiom (forall m: Map, m': Map::
  { Map#Equal(m, m') }
    Map#Equal(m, m') ==> m == m');

function Map#Disjoint(Map, Map): bool;
axiom (forall m: Map, m': Map ::
  { Map#Disjoint(m, m') }
    Map#Disjoint(m, m') <==>
    (forall o: Box :: {Set#IsMember(Map#Domain(m), o)} {Set#IsMember(Map#Domain(m'), o)} !Set#IsMember(Map#Domain(m), o) || !Set#IsMember(Map#Domain(m'), o)));

// ---------------------------------------------------------------
// -- Axiomatization of IMaps ------------------------------------
// ---------------------------------------------------------------

type IMap;

// A IMap is defined by two functions, Map#Domain and Map#Elements.

function IMap#Domain(IMap) : ISet;

function IMap#Elements(IMap) : [Box]Box;

axiom (forall m: IMap ::
  { IMap#Domain(m) }
  m == IMap#Empty() || (exists k: Box :: IMap#Domain(m)[k]));
axiom (forall m: IMap ::
  { IMap#Values(m) }
  m == IMap#Empty() || (exists v: Box :: IMap#Values(m)[v]));
axiom (forall m: IMap ::
  { IMap#Items(m) }
  m == IMap#Empty() || (exists k, v: Box :: IMap#Items(m)[$Box(#_System._tuple#2._#Make2(k, v))]));

axiom (forall m: IMap ::
  { IMap#Domain(m) }
  m == IMap#Empty() <==> IMap#Domain(m) == ISet#Empty());
axiom (forall m: IMap ::
  { IMap#Values(m) }
  m == IMap#Empty() <==> IMap#Values(m) == ISet#Empty());
axiom (forall m: IMap ::
  { IMap#Items(m) }
  m == IMap#Empty() <==> IMap#Items(m) == ISet#Empty());

// The set of Values of an IMap can be obtained by the function IMap#Values, which is
// defined as follows.  Remember, an ISet is defined by membership (using Boogie's
// square brackets) so we need to define what these mean for the ISet
// returned by IMap#Values.

function IMap#Values(IMap) : ISet;

axiom (forall m: IMap, v: Box :: { IMap#Values(m)[v] }
  IMap#Values(m)[v] ==
	(exists u: Box :: { IMap#Domain(m)[u] } { IMap#Elements(m)[u] }
	  IMap#Domain(m)[u] &&
    v == IMap#Elements(m)[u]));

// The set of Items--that is, (key,value) pairs--of a Map can be obtained by the
// function IMap#Items. Function IMap#Items returns a set of
// pairs, and the axiomatization of pairs is Dafny specific.  Therefore, the
// definition of IMap#Items here is to be considered Dafny specific.  Also, note
// that it relies on the two destructors for 2-tuples.

function IMap#Items(IMap) : ISet;

axiom (forall m: IMap, item: Box :: { IMap#Items(m)[item] }
  IMap#Items(m)[item] <==>
    IMap#Domain(m)[_System.Tuple2._0($Unbox(item))] &&
    IMap#Elements(m)[_System.Tuple2._0($Unbox(item))] == _System.Tuple2._1($Unbox(item)));

// Here are the operations that produce Map values.
function IMap#Empty(): IMap;
axiom (forall u: Box ::
        { IMap#Domain(IMap#Empty(): IMap)[u] }
        !IMap#Domain(IMap#Empty(): IMap)[u]);

function IMap#Glue([Box] bool, [Box]Box, Ty): IMap;
axiom (forall a: [Box]bool, b: [Box]Box, t: Ty ::
  { IMap#Domain(IMap#Glue(a, b, t)) }
  IMap#Domain(IMap#Glue(a, b, t)) == a);
axiom (forall a: [Box]bool, b: [Box]Box, t: Ty ::
  { IMap#Elements(IMap#Glue(a, b, t)) }
  IMap#Elements(IMap#Glue(a, b, t)) == b);
axiom (forall a: [Box]bool, b: [Box]Box, t0, t1: Ty ::
  { IMap#Glue(a, b, TIMap(t0, t1)) }
  // In the following line, no trigger needed, since the quantifier only gets used in negative contexts
  (forall bx: Box :: a[bx] ==> $IsBox(bx, t0) && $IsBox(b[bx], t1))
  ==>
  $Is(IMap#Glue(a, b, TIMap(t0, t1)), TIMap(t0, t1)));

//Build is used in displays
function IMap#Build(IMap, Box, Box): IMap;
/*axiom (forall m: IMap, u: Box, v: Box ::
  { IMap#Domain(IMap#Build(m, u, v))[u] } { IMap#Elements(IMap#Build(m, u, v))[u] }
  IMap#Domain(IMap#Build(m, u, v))[u] && IMap#Elements(IMap#Build(m, u, v))[u] == v);*/

axiom (forall m: IMap, u: Box, u': Box, v: Box ::
  { IMap#Domain(IMap#Build(m, u, v))[u'] } { IMap#Elements(IMap#Build(m, u, v))[u'] }
  (u' == u ==> IMap#Domain(IMap#Build(m, u, v))[u'] &&
               IMap#Elements(IMap#Build(m, u, v))[u'] == v) &&
  (u' != u ==> IMap#Domain(IMap#Build(m, u, v))[u'] == IMap#Domain(m)[u'] &&
               IMap#Elements(IMap#Build(m, u, v))[u'] == IMap#Elements(m)[u']));

//equality for imaps
function IMap#Equal(IMap, IMap): bool;
axiom (forall m: IMap, m': IMap::
  { IMap#Equal(m, m') }
    IMap#Equal(m, m') <==> (forall u : Box :: IMap#Domain(m)[u] == IMap#Domain(m')[u]) &&
                          (forall u : Box :: IMap#Domain(m)[u] ==> IMap#Elements(m)[u] == IMap#Elements(m')[u]));
// extensionality
axiom (forall m: IMap, m': IMap::
  { IMap#Equal(m, m') }
    IMap#Equal(m, m') ==> m == m');

// IMap operations
function IMap#Merge(IMap, IMap): IMap;
axiom (forall m: IMap, n: IMap ::
  { IMap#Domain(IMap#Merge(m, n)) }
  IMap#Domain(IMap#Merge(m, n)) == ISet#Union(IMap#Domain(m), IMap#Domain(n)));
axiom (forall m: IMap, n: IMap, u: Box ::
  { IMap#Elements(IMap#Merge(m, n))[u] }
  IMap#Domain(IMap#Merge(m, n))[u] ==>
    (!IMap#Domain(n)[u] ==> IMap#Elements(IMap#Merge(m, n))[u] == IMap#Elements(m)[u]) &&
    (IMap#Domain(n)[u] ==> IMap#Elements(IMap#Merge(m, n))[u] == IMap#Elements(n)[u]));

function IMap#Subtract(IMap, Set): IMap;
axiom (forall m: IMap, s: Set ::
  { IMap#Domain(IMap#Subtract(m, s)) }
  IMap#Domain(IMap#Subtract(m, s)) == ISet#Difference(IMap#Domain(m), ISet#FromSet(s)));
axiom (forall m: IMap, s: Set, u: Box ::
  { IMap#Elements(IMap#Subtract(m, s))[u] }
  IMap#Domain(IMap#Subtract(m, s))[u] ==>
    IMap#Elements(IMap#Subtract(m, s))[u] == IMap#Elements(m)[u]);

// -------------------------------------------------------------------------
// -- Provide arithmetic wrappers to improve triggering and non-linear math
// -------------------------------------------------------------------------

function INTERNAL_add_boogie(x:int, y:int) : int { x + y }
function INTERNAL_sub_boogie(x:int, y:int) : int { x - y }
function INTERNAL_mul_boogie(x:int, y:int) : int { x * y }
function INTERNAL_div_boogie(x:int, y:int) : int { x div y }
function INTERNAL_mod_boogie(x:int, y:int) : int { x mod y }
function {:never_pattern true} INTERNAL_lt_boogie(x:int, y:int) : bool { x < y }
function {:never_pattern true} INTERNAL_le_boogie(x:int, y:int) : bool { x <= y }
function {:never_pattern true} INTERNAL_gt_boogie(x:int, y:int) : bool { x > y }
function {:never_pattern true} INTERNAL_ge_boogie(x:int, y:int) : bool { x >= y }

function Mul(x, y: int): int { x * y }
function Div(x, y: int): int { x div y }
function Mod(x, y: int): int { x mod y }
function Add(x, y: int): int { x + y }
function Sub(x, y: int): int { x - y }

#if ARITH_DISTR
axiom (forall x, y, z: int ::
  { Mul(Add(x, y), z) }
  Mul(Add(x, y), z) == Add(Mul(x, z), Mul(y, z)));
axiom (forall x,y,z: int ::
  { Mul(x, Add(y, z)) }
  Mul(x, Add(y, z)) == Add(Mul(x, y), Mul(x, z)));
//axiom (forall x, y, z: int ::
//  { Mul(Sub(x, y), z) }
//  Mul(Sub(x, y), z) == Sub(Mul(x, z), Mul(y, z)));
#endif
#if ARITH_MUL_DIV_MOD
axiom (forall x, y: int ::
  { Div(x, y), Mod(x, y) }
  { Mul(Div(x, y), y) }
  y != 0 ==>
  Mul(Div(x, y), y) + Mod(x, y) == x);
#endif
#if ARITH_MUL_SIGN
axiom (forall x, y: int ::
  { Mul(x, y) }
  ((0 <= x && 0 <= y) || (x <= 0 && y <= 0) ==> 0 <= Mul(x, y)));
#endif
#if ARITH_MUL_COMM
axiom (forall x, y: int ::
  { Mul(x, y) }
  Mul(x, y) == Mul(y, x));
#endif
#if ARITH_MUL_ASSOC
axiom (forall x, y, z: int ::
  { Mul(x, Mul(y, z)) }
  Mul(y, z) != z && Mul(y, z) != y ==> Mul(x, Mul(y, z)) == Mul(Mul(x, y), z));
#endif

// -------------------------------------------------------------------------
