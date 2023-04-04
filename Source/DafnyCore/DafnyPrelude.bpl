// Dafny prelude
// Created 9 February 2008 by Rustan Leino.
// Converted to Boogie 2 on 28 June 2008.
// Edited sequence axioms 20 October 2009 by Alex Summers.
// Modified 2014 by Dan Rosen.
// Copyright (c) 2008-2014, Microsoft.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

const $$Language$Dafny: bool;  // To be recognizable to the ModelViewer as
axiom $$Language$Dafny;        // coming from a Dafny program.

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
function TBitvector(int) : Ty uses {
  axiom (forall w: int :: { TBitvector(w) } Inv0_TBitvector(TBitvector(w)) == w);
}
function TSet(Ty)      : Ty uses {
  axiom (forall t: Ty :: { TSet(t) } Inv0_TSet(TSet(t)) == t);
  axiom (forall t: Ty    :: { TSet(t) }      Tag(TSet(t))      == TagSet);
}
function TISet(Ty)     : Ty uses {
  axiom (forall t: Ty :: { TISet(t) } Inv0_TISet(TISet(t)) == t);
  axiom (forall t: Ty    :: { TISet(t) }     Tag(TISet(t))     == TagISet);
}
function TMultiSet(Ty) : Ty uses {
  axiom (forall t: Ty :: { TMultiSet(t) } Inv0_TMultiSet(TMultiSet(t)) == t);
  axiom (forall t: Ty    :: { TMultiSet(t) } Tag(TMultiSet(t)) == TagMultiSet);
}
function TSeq(Ty)      : Ty uses {
  axiom (forall t: Ty :: { TSeq(t) } Inv0_TSeq(TSeq(t)) == t);
  axiom (forall t: Ty    :: { TSeq(t) }      Tag(TSeq(t))      == TagSeq);
}
function TMap(Ty, Ty)  : Ty uses {
  axiom (forall t, u: Ty :: { TMap(t,u) } Inv0_TMap(TMap(t,u)) == t);
  axiom (forall t, u: Ty :: { TMap(t,u) } Inv1_TMap(TMap(t,u)) == u);
  axiom (forall t, u: Ty :: { TMap(t,u) }    Tag(TMap(t,u))    == TagMap);
}
function TIMap(Ty, Ty) : Ty uses {
  axiom (forall t, u: Ty :: { TIMap(t,u) } Inv0_TIMap(TIMap(t,u)) == t);
  axiom (forall t, u: Ty :: { TIMap(t,u) } Inv1_TIMap(TIMap(t,u)) == u);
  axiom (forall t, u: Ty :: { TIMap(t,u) }   Tag(TIMap(t,u))   == TagIMap);
}

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
function {:identity} Lit<T>(x: T): T { x } uses {
  axiom (forall<T> x: T :: { $Box(Lit(x)) } $Box(Lit(x)) == Lit($Box(x)) );
}

// Specialize Lit to concrete types.
// These aren't logically required, but on some examples improve
// verification speed
function {:identity} LitInt(x: int): int { x } uses {
  axiom (forall x: int :: { $Box(LitInt(x)) } $Box(LitInt(x)) == Lit($Box(x)) );
}
function {:identity} LitReal(x: real): real { x } uses {
  axiom (forall x: real :: { $Box(LitReal(x)) } $Box(LitReal(x)) == Lit($Box(x)) );
}

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
function char#FromInt(int): char uses {
  axiom (forall n: int ::
    { char#FromInt(n) }
    char#IsChar(n) ==> char#ToInt(char#FromInt(n)) == n);
}

function char#ToInt(char): int uses {
  axiom (forall ch: char ::
    { char#ToInt(ch) }
    char#FromInt(char#ToInt(ch)) == ch &&
    char#IsChar(char#ToInt(ch)));
}  

function char#Plus(char, char): char uses {
  axiom (forall a: char, b: char ::
    { char#Plus(a, b) }
    char#Plus(a, b) == char#FromInt(char#ToInt(a) + char#ToInt(b)));
}
function char#Minus(char, char): char uses {
  axiom (forall a: char, b: char ::
    { char#Minus(a, b) }
    char#Minus(a, b) == char#FromInt(char#ToInt(a) - char#ToInt(b)));
}

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

function $Box<T>(T): Box uses {
  axiom (forall<T> x : T :: { $Box(x) } $Unbox($Box(x)) == x);
}
function $Unbox<T>(Box): T;

// Corresponding entries for boxes...
// This could probably be solved by having Box also inhabit Ty
function $IsBox<T>(T,Ty): bool;
function $IsAllocBox<T>(T,Ty,Heap): bool;

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
    ( $IsBox(bx, TBitvector(0)) ==> $Box($Unbox(bx) : Bv0) == bx && $Is($Unbox(bx) : Set Box, TBitvector(0))));

axiom (forall bx : Box, t : Ty ::
    { $IsBox(bx, TSet(t)) }
    ( $IsBox(bx, TSet(t)) ==> $Box($Unbox(bx) : Set Box) == bx && $Is($Unbox(bx) : Set Box, TSet(t))));
axiom (forall bx : Box, t : Ty ::
    { $IsBox(bx, TISet(t)) }
    ( $IsBox(bx, TISet(t)) ==> $Box($Unbox(bx) : ISet Box) == bx && $Is($Unbox(bx) : ISet Box, TISet(t))));
axiom (forall bx : Box, t : Ty ::
    { $IsBox(bx, TMultiSet(t)) }
    ( $IsBox(bx, TMultiSet(t)) ==> $Box($Unbox(bx) : MultiSet Box) == bx && $Is($Unbox(bx) : MultiSet Box, TMultiSet(t))));
axiom (forall bx : Box, t : Ty ::
    { $IsBox(bx, TSeq(t)) }
    ( $IsBox(bx, TSeq(t)) ==> $Box($Unbox(bx) : Seq Box) == bx && $Is($Unbox(bx) : Seq Box, TSeq(t))));
axiom (forall bx : Box, s : Ty, t : Ty ::
    { $IsBox(bx, TMap(s, t)) }
    ( $IsBox(bx, TMap(s, t)) ==> $Box($Unbox(bx) : Map Box Box) == bx && $Is($Unbox(bx) : Map Box Box, TMap(s, t))));
axiom (forall bx : Box, s : Ty, t : Ty ::
    { $IsBox(bx, TIMap(s, t)) }
    ( $IsBox(bx, TIMap(s, t)) ==> $Box($Unbox(bx) : IMap Box Box) == bx && $Is($Unbox(bx) : IMap Box Box, TIMap(s, t))));

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
function $Is<T>(T,Ty): bool uses {           // no heap for now
    axiom(forall v : int  :: { $Is(v,TInt) }  $Is(v,TInt));
    axiom(forall v : real :: { $Is(v,TReal) } $Is(v,TReal));
    axiom(forall v : bool :: { $Is(v,TBool) } $Is(v,TBool));
    axiom(forall v : char :: { $Is(v,TChar) } $Is(v,TChar));
    axiom(forall v : ORDINAL :: { $Is(v,TORDINAL) } $Is(v,TORDINAL));
    
    // Since every bitvector type is a separate type in Boogie, the $Is/$IsAlloc axioms
    // for bitvectors are generated programatically. Except, TBitvector(0) is given here.
    axiom (forall v: Bv0 :: { $Is(v, TBitvector(0)) } $Is(v, TBitvector(0)));

    axiom (forall v: Set Box, t0: Ty :: { $Is(v, TSet(t0)) }
      $Is(v, TSet(t0)) <==>
      (forall bx: Box :: { v[bx] }
        v[bx] ==> $IsBox(bx, t0)));
    axiom (forall v: ISet Box, t0: Ty :: { $Is(v, TISet(t0)) }
      $Is(v, TISet(t0)) <==>
      (forall bx: Box :: { v[bx] }
        v[bx] ==> $IsBox(bx, t0)));
    axiom (forall v: MultiSet Box, t0: Ty :: { $Is(v, TMultiSet(t0)) }
      $Is(v, TMultiSet(t0)) <==>
      (forall bx: Box :: { v[bx] }
        0 < v[bx] ==> $IsBox(bx, t0)));
    axiom (forall v: MultiSet Box, t0: Ty :: { $Is(v, TMultiSet(t0)) }
      $Is(v, TMultiSet(t0)) ==> $IsGoodMultiSet(v));
    axiom (forall v: Seq Box, t0: Ty :: { $Is(v, TSeq(t0)) }
      $Is(v, TSeq(t0)) <==>
      (forall i : int :: { Seq#Index(v, i) }
        0 <= i && i < Seq#Length(v) ==>
        $IsBox(Seq#Index(v, i), t0)));
        
    axiom (forall v: Map Box Box, t0: Ty, t1: Ty ::
      { $Is(v, TMap(t0, t1)) }
      $Is(v, TMap(t0, t1))
         <==> (forall bx: Box ::
          { Map#Elements(v)[bx] } { Map#Domain(v)[bx] }
          Map#Domain(v)[bx] ==>
            $IsBox(Map#Elements(v)[bx], t1) &&
            $IsBox(bx, t0)));
            
    axiom (forall v: Map Box Box, t0: Ty, t1: Ty ::
      { $Is(v, TMap(t0, t1)) }
      $Is(v, TMap(t0, t1)) ==>
        $Is(Map#Domain(v), TSet(t0)) &&
        $Is(Map#Values(v), TSet(t1)) &&
        $Is(Map#Items(v), TSet(Tclass._System.Tuple2(t0, t1))));
    axiom (forall v: IMap Box Box, t0: Ty, t1: Ty ::
      { $Is(v, TIMap(t0, t1)) }
      $Is(v, TIMap(t0, t1))
         <==> (forall bx: Box ::
          { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] }
          IMap#Domain(v)[bx] ==>
            $IsBox(IMap#Elements(v)[bx], t1) &&
            $IsBox(bx, t0)));
    axiom (forall v: IMap Box Box, t0: Ty, t1: Ty ::
      { $Is(v, TIMap(t0, t1)) }
      $Is(v, TIMap(t0, t1)) ==>
        $Is(IMap#Domain(v), TISet(t0)) &&
        $Is(IMap#Values(v), TISet(t1)) &&
        $Is(IMap#Items(v), TISet(Tclass._System.Tuple2(t0, t1))));
}
function $IsAlloc<T>(T,Ty,Heap): bool uses {
    axiom(forall h : Heap, v : int  :: { $IsAlloc(v,TInt,h) }  $IsAlloc(v,TInt,h));
    axiom(forall h : Heap, v : real :: { $IsAlloc(v,TReal,h) } $IsAlloc(v,TReal,h));
    axiom(forall h : Heap, v : bool :: { $IsAlloc(v,TBool,h) } $IsAlloc(v,TBool,h));
    axiom(forall h : Heap, v : char :: { $IsAlloc(v,TChar,h) } $IsAlloc(v,TChar,h));
    axiom(forall h : Heap, v : ORDINAL :: { $IsAlloc(v,TORDINAL,h) } $IsAlloc(v,TORDINAL,h));
    
    axiom (forall v: Bv0, h: Heap :: { $IsAlloc(v, TBitvector(0), h) } $IsAlloc(v, TBitvector(0), h));
    
    axiom (forall v: Set Box, t0: Ty, h: Heap :: { $IsAlloc(v, TSet(t0), h) }
      $IsAlloc(v, TSet(t0), h) <==>
      (forall bx: Box :: { v[bx] }
        v[bx] ==> $IsAllocBox(bx, t0, h)));
    axiom (forall v: ISet Box, t0: Ty, h: Heap :: { $IsAlloc(v, TISet(t0), h) }
      $IsAlloc(v, TISet(t0), h) <==>
      (forall bx: Box :: { v[bx] }
        v[bx] ==> $IsAllocBox(bx, t0, h)));
    axiom (forall v: MultiSet Box, t0: Ty, h: Heap :: { $IsAlloc(v, TMultiSet(t0), h) }
      $IsAlloc(v, TMultiSet(t0), h) <==>
      (forall bx: Box :: { v[bx] }
        0 < v[bx] ==> $IsAllocBox(bx, t0, h)));
    axiom (forall v: Seq Box, t0: Ty, h: Heap :: { $IsAlloc(v, TSeq(t0), h) }
      $IsAlloc(v, TSeq(t0), h) <==>
      (forall i : int :: { Seq#Index(v, i) }
        0 <= i && i < Seq#Length(v) ==>
    	$IsAllocBox(Seq#Index(v, i), t0, h)));
    	
    axiom (forall v: Map Box Box, t0: Ty, t1: Ty, h: Heap ::
      { $IsAlloc(v, TMap(t0, t1), h) }
      $IsAlloc(v, TMap(t0, t1), h)
         <==> (forall bx: Box ::
          { Map#Elements(v)[bx] } { Map#Domain(v)[bx] }
          Map#Domain(v)[bx] ==>
            $IsAllocBox(Map#Elements(v)[bx], t1, h) &&
            $IsAllocBox(bx, t0, h)));
            
    axiom (forall v: IMap Box Box, t0: Ty, t1: Ty, h: Heap ::
      { $IsAlloc(v, TIMap(t0, t1), h) }
      $IsAlloc(v, TIMap(t0, t1), h)
         <==> (forall bx: Box ::
          { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] }
          IMap#Domain(v)[bx] ==>
            $IsAllocBox(IMap#Elements(v)[bx], t1, h) &&
            $IsAllocBox(bx, t0, h)));
}

function $AlwaysAllocated(Ty): bool uses {
    axiom (forall ty: Ty :: { $AlwaysAllocated(ty) }
      $AlwaysAllocated(ty) ==>
      (forall h: Heap, v: Box  :: { $IsAllocBox(v, ty, h) }  $IsBox(v, ty) ==> $IsAllocBox(v, ty, h)));
}

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

function SetRef_to_SetBox(s: [ref]bool): Set Box;
axiom (forall s: [ref]bool, bx: Box :: { SetRef_to_SetBox(s)[bx] }
  SetRef_to_SetBox(s)[bx] == s[$Unbox(bx): ref]);
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
// o-m-n == o+(m+n)
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
// -- Axiom contexts ---------------------------------------------
// ---------------------------------------------------------------

// used to make sure function axioms are not used while their consistency is being checked
const $ModuleContextHeight: int;
const $FunctionContextHeight: int;

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
// -- Opaqueness encoding ----------------------------------------
// ---------------------------------------------------------------

function CanRevealFuel(LayerType, bool) : LayerType;

axiom (forall $ly: LayerType :: 
  { CanRevealFuel($LS($ly), true) }
  CanRevealFuel($LS($ly), true) == $LS(CanRevealFuel($ly, true)));

axiom (forall $ly: LayerType, b: bool ::
  { CanRevealFuel(AsFuelBottom($ly), b) }
  CanRevealFuel(AsFuelBottom($ly), b)
  == AsFuelBottom(CanRevealFuel($ly, b)));
  
// ---------------------------------------------------------------
// -- Fields -----------------------------------------------------
// ---------------------------------------------------------------

type Field alpha;

function FDim<T>(Field T): int uses {
  axiom FDim(alloc) == 0;
}

function IndexField(int): Field Box;
axiom (forall i: int :: { IndexField(i) } FDim(IndexField(i)) == 1);
function IndexField_Inverse<T>(Field T): int;
axiom (forall i: int :: { IndexField(i) } IndexField_Inverse(IndexField(i)) == i);

function MultiIndexField(Field Box, int): Field Box;
axiom (forall f: Field Box, i: int :: { MultiIndexField(f,i) } FDim(MultiIndexField(f,i)) == FDim(f) + 1);
function MultiIndexField_Inverse0<T>(Field T): Field T;
function MultiIndexField_Inverse1<T>(Field T): int;
axiom (forall f: Field Box, i: int :: { MultiIndexField(f,i) }
  MultiIndexField_Inverse0(MultiIndexField(f,i)) == f &&
  MultiIndexField_Inverse1(MultiIndexField(f,i)) == i);

function DeclType<T>(Field T): ClassName;

type NameFamily;
function DeclName<T>(Field T): NameFamily uses {
  axiom DeclName(alloc) == allocName;
}
function FieldOfDecl<alpha>(ClassName, NameFamily): Field alpha;
axiom (forall<T> cl : ClassName, nm: NameFamily ::
   {FieldOfDecl(cl, nm): Field T}
   DeclType(FieldOfDecl(cl, nm): Field T) == cl && DeclName(FieldOfDecl(cl, nm): Field T) == nm);

function $IsGhostField<T>(Field T): bool uses {
   axiom $IsGhostField(alloc); // treat as ghost field, since it is allowed to be changed by ghost code
  
   axiom (forall h: Heap, k: Heap :: { $HeapSuccGhost(h,k) }
      $HeapSuccGhost(h,k) ==>
        $HeapSucc(h,k) &&
        (forall<alpha> o: ref, f: Field alpha :: { read(k, o, f) }
          !$IsGhostField(f) ==> read(h, o, f) == read(k, o, f)));
}

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

const unique alloc: Field bool;
const unique allocName: NameFamily;

// ---------------------------------------------------------------
// -- Arrays -----------------------------------------------------
// ---------------------------------------------------------------

function _System.array.Length(a: ref): int uses {
  axiom (forall o: ref :: 0 <= _System.array.Length(o));
}

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
type Heap = [ref]<alpha>[Field alpha]alpha;
function {:inline} read<alpha>(H:Heap, r:ref, f:Field alpha): alpha { H[r][f] }
function {:inline} update<alpha>(H:Heap, r:ref, f:Field alpha, v:alpha): Heap { H[r := H[r][f := v]] }

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
axiom (forall<alpha> h: Heap, r: ref, f: Field alpha, x: alpha :: { update(h, r, f, x) }
  $IsGoodHeap(update(h, r, f, x)) ==>
  $HeapSucc(h, update(h, r, f, x)));
axiom (forall a,b,c: Heap :: { $HeapSucc(a,b), $HeapSucc(b,c) }
  a != c ==> $HeapSucc(a,b) && $HeapSucc(b,c) ==> $HeapSucc(a,c));
axiom (forall h: Heap, k: Heap :: { $HeapSucc(h,k) }
  $HeapSucc(h,k) ==> (forall o: ref :: { read(k, o, alloc) } read(h, o, alloc) ==> read(k, o, alloc)));

function $HeapSuccGhost(Heap, Heap): bool;

// ---------------------------------------------------------------
// -- Non-determinism --------------------------------------------
// ---------------------------------------------------------------

type TickType;
var $Tick: TickType;

// ---------------------------------------------------------------
// -- Useful macros ----------------------------------------------
// ---------------------------------------------------------------

// havoc everything in $Heap, except {this}+rds+nw
procedure $YieldHavoc(this: ref, rds: Set Box, nw: Set Box);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha :: { read($Heap, $o, $f) }
            $o != null && read(old($Heap), $o, alloc) ==>
            $o == this || rds[$Box($o)] || nw[$Box($o)] ==>
              read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);

// havoc everything in $Heap, except rds-modi-{this}
procedure $IterHavoc0(this: ref, rds: Set Box, modi: Set Box);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha :: { read($Heap, $o, $f) }
            $o != null && read(old($Heap), $o, alloc) ==>
            rds[$Box($o)] && !modi[$Box($o)] && $o != this ==>
              read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);

// havoc $Heap at {this}+modi+nw
procedure $IterHavoc1(this: ref, modi: Set Box, nw: Set Box);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha :: { read($Heap, $o, $f) }
            $o != null && read(old($Heap), $o, alloc) ==>
              read($Heap, $o, $f) == read(old($Heap), $o, $f) ||
              $o == this || modi[$Box($o)] || nw[$Box($o)]);
  ensures $HeapSucc(old($Heap), $Heap);

procedure $IterCollectNewObjects(prevHeap: Heap, newHeap: Heap, this: ref, NW: Field (Set Box))
                        returns (s: Set Box);
  ensures (forall bx: Box :: { s[bx] } s[bx] <==>
              read(newHeap, this, NW)[bx] ||
              ($Unbox(bx) != null && !read(prevHeap, $Unbox(bx):ref, alloc) && read(newHeap, $Unbox(bx):ref, alloc)));

// ---------------------------------------------------------------
// -- Axiomatizations --------------------------------------------
// ---------------------------------------------------------------

// ---------------------------------------------------------------
// -- Axiomatization of sets -------------------------------------
// ---------------------------------------------------------------

type Set T = [T]bool;

function Set#Card<T>(Set T): int;
axiom (forall<T> s: Set T :: { Set#Card(s) } 0 <= Set#Card(s));

function Set#Empty<T>(): Set T;
axiom (forall<T> o: T :: { Set#Empty()[o] } !Set#Empty()[o]);
axiom (forall<T> s: Set T :: { Set#Card(s) }
  (Set#Card(s) == 0 <==> s == Set#Empty()) &&
  (Set#Card(s) != 0 ==> (exists x: T :: s[x])));

// the empty set could be of anything
//axiom (forall<T> t: Ty :: { $Is(Set#Empty() : [T]bool, TSet(t)) } $Is(Set#Empty() : [T]bool, TSet(t)));

function Set#Singleton<T>(T): Set T;
axiom (forall<T> r: T :: { Set#Singleton(r) } Set#Singleton(r)[r]);
axiom (forall<T> r: T, o: T :: { Set#Singleton(r)[o] } Set#Singleton(r)[o] <==> r == o);
axiom (forall<T> r: T :: { Set#Card(Set#Singleton(r)) } Set#Card(Set#Singleton(r)) == 1);

function Set#UnionOne<T>(Set T, T): Set T;
axiom (forall<T> a: Set T, x: T, o: T :: { Set#UnionOne(a,x)[o] }
  Set#UnionOne(a,x)[o] <==> o == x || a[o]);
axiom (forall<T> a: Set T, x: T :: { Set#UnionOne(a, x) }
  Set#UnionOne(a, x)[x]);
axiom (forall<T> a: Set T, x: T, y: T :: { Set#UnionOne(a, x), a[y] }
  a[y] ==> Set#UnionOne(a, x)[y]);
axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#UnionOne(a, x)) }
  a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a));
axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#UnionOne(a, x)) }
  !a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a) + 1);

function Set#Union<T>(Set T, Set T): Set T;
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Union(a,b)[o] }
  Set#Union(a,b)[o] <==> a[o] || b[o]);
axiom (forall<T> a, b: Set T, y: T :: { Set#Union(a, b), a[y] }
  a[y] ==> Set#Union(a, b)[y]);
axiom (forall<T> a, b: Set T, y: T :: { Set#Union(a, b), b[y] }
  b[y] ==> Set#Union(a, b)[y]);
axiom (forall<T> a, b: Set T :: { Set#Union(a, b) }
  Set#Disjoint(a, b) ==>
    Set#Difference(Set#Union(a, b), a) == b &&
    Set#Difference(Set#Union(a, b), b) == a);
// Follows from the general union axiom, but might be still worth including, because disjoint union is a common case:
// axiom (forall<T> a, b: Set T :: { Set#Card(Set#Union(a, b)) }
//   Set#Disjoint(a, b) ==>
//     Set#Card(Set#Union(a, b)) == Set#Card(a) + Set#Card(b));

function Set#Intersection<T>(Set T, Set T): Set T;
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Intersection(a,b)[o] }
  Set#Intersection(a,b)[o] <==> a[o] && b[o]);

axiom (forall<T> a, b: Set T :: { Set#Union(Set#Union(a, b), b) }
  Set#Union(Set#Union(a, b), b) == Set#Union(a, b));
axiom (forall<T> a, b: Set T :: { Set#Union(a, Set#Union(a, b)) }
  Set#Union(a, Set#Union(a, b)) == Set#Union(a, b));
axiom (forall<T> a, b: Set T :: { Set#Intersection(Set#Intersection(a, b), b) }
  Set#Intersection(Set#Intersection(a, b), b) == Set#Intersection(a, b));
axiom (forall<T> a, b: Set T :: { Set#Intersection(a, Set#Intersection(a, b)) }
  Set#Intersection(a, Set#Intersection(a, b)) == Set#Intersection(a, b));
axiom (forall<T> a, b: Set T :: { Set#Card(Set#Union(a, b)) }{ Set#Card(Set#Intersection(a, b)) }
  Set#Card(Set#Union(a, b)) + Set#Card(Set#Intersection(a, b)) == Set#Card(a) + Set#Card(b));

function Set#Difference<T>(Set T, Set T): Set T;
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Difference(a,b)[o] }
  Set#Difference(a,b)[o] <==> a[o] && !b[o]);
axiom (forall<T> a, b: Set T, y: T :: { Set#Difference(a, b), b[y] }
  b[y] ==> !Set#Difference(a, b)[y] );
axiom (forall<T> a, b: Set T ::
  { Set#Card(Set#Difference(a, b)) }
  Set#Card(Set#Difference(a, b)) + Set#Card(Set#Difference(b, a))
  + Set#Card(Set#Intersection(a, b))
    == Set#Card(Set#Union(a, b)) &&
  Set#Card(Set#Difference(a, b)) == Set#Card(a) - Set#Card(Set#Intersection(a, b)));

function Set#Subset<T>(Set T, Set T): bool;
axiom (forall<T> a: Set T, b: Set T :: { Set#Subset(a,b) }
  Set#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] ==> b[o]));
// axiom(forall<T> a: Set T, b: Set T ::
//   { Set#Subset(a,b), Set#Card(a), Set#Card(b) }  // very restrictive trigger
//   Set#Subset(a,b) ==> Set#Card(a) <= Set#Card(b));


function Set#Equal<T>(Set T, Set T): bool;
axiom (forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }
  Set#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <==> b[o]));
axiom (forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }  // extensionality axiom for sets
  Set#Equal(a,b) ==> a == b);

function Set#Disjoint<T>(Set T, Set T): bool;
axiom (forall<T> a: Set T, b: Set T :: { Set#Disjoint(a,b) }
  Set#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} !a[o] || !b[o]));

// ---------------------------------------------------------------
// -- Axiomatization of isets -------------------------------------
// ---------------------------------------------------------------

type ISet T = [T]bool;

function ISet#Empty<T>(): Set T;
axiom (forall<T> o: T :: { ISet#Empty()[o] } !ISet#Empty()[o]);

// the empty set could be of anything
//axiom (forall<T> t: Ty :: { $Is(ISet#Empty() : [T]bool, TISet(t)) } $Is(ISet#Empty() : [T]bool, TISet(t)));


function ISet#UnionOne<T>(ISet T, T): ISet T;
axiom (forall<T> a: ISet T, x: T, o: T :: { ISet#UnionOne(a,x)[o] }
  ISet#UnionOne(a,x)[o] <==> o == x || a[o]);
axiom (forall<T> a: ISet T, x: T :: { ISet#UnionOne(a, x) }
  ISet#UnionOne(a, x)[x]);
axiom (forall<T> a: ISet T, x: T, y: T :: { ISet#UnionOne(a, x), a[y] }
  a[y] ==> ISet#UnionOne(a, x)[y]);

function ISet#Union<T>(ISet T, ISet T): ISet T;
axiom (forall<T> a: ISet T, b: ISet T, o: T :: { ISet#Union(a,b)[o] }
  ISet#Union(a,b)[o] <==> a[o] || b[o]);
axiom (forall<T> a, b: ISet T, y: T :: { ISet#Union(a, b), a[y] }
  a[y] ==> ISet#Union(a, b)[y]);
axiom (forall<T> a, b: Set T, y: T :: { ISet#Union(a, b), b[y] }
  b[y] ==> ISet#Union(a, b)[y]);
axiom (forall<T> a, b: ISet T :: { ISet#Union(a, b) }
  ISet#Disjoint(a, b) ==>
    ISet#Difference(ISet#Union(a, b), a) == b &&
    ISet#Difference(ISet#Union(a, b), b) == a);

function ISet#Intersection<T>(ISet T, ISet T): ISet T;
axiom (forall<T> a: ISet T, b: ISet T, o: T :: { ISet#Intersection(a,b)[o] }
  ISet#Intersection(a,b)[o] <==> a[o] && b[o]);

axiom (forall<T> a, b: ISet T :: { ISet#Union(ISet#Union(a, b), b) }
  ISet#Union(ISet#Union(a, b), b) == ISet#Union(a, b));
axiom (forall<T> a, b: Set T :: { ISet#Union(a, ISet#Union(a, b)) }
  ISet#Union(a, ISet#Union(a, b)) == ISet#Union(a, b));
axiom (forall<T> a, b: ISet T :: { ISet#Intersection(ISet#Intersection(a, b), b) }
  ISet#Intersection(ISet#Intersection(a, b), b) == ISet#Intersection(a, b));
axiom (forall<T> a, b: ISet T :: { ISet#Intersection(a, ISet#Intersection(a, b)) }
  ISet#Intersection(a, ISet#Intersection(a, b)) == ISet#Intersection(a, b));


function ISet#Difference<T>(ISet T, ISet T): ISet T;
axiom (forall<T> a: ISet T, b: ISet T, o: T :: { ISet#Difference(a,b)[o] }
  ISet#Difference(a,b)[o] <==> a[o] && !b[o]);
axiom (forall<T> a, b: ISet T, y: T :: { ISet#Difference(a, b), b[y] }
  b[y] ==> !ISet#Difference(a, b)[y] );

function ISet#Subset<T>(ISet T, ISet T): bool;
axiom (forall<T> a: ISet T, b: ISet T :: { ISet#Subset(a,b) }
  ISet#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] ==> b[o]));

function ISet#Equal<T>(ISet T, ISet T): bool;
axiom (forall<T> a: ISet T, b: ISet T :: { ISet#Equal(a,b) }
  ISet#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <==> b[o]));
axiom (forall<T> a: ISet T, b: ISet T :: { ISet#Equal(a,b) }  // extensionality axiom for sets
  ISet#Equal(a,b) ==> a == b);

function ISet#Disjoint<T>(ISet T, ISet T): bool;
axiom (forall<T> a: ISet T, b: ISet T :: { ISet#Disjoint(a,b) }
  ISet#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} !a[o] || !b[o]));

// ---------------------------------------------------------------
// -- Axiomatization of multisets --------------------------------
// ---------------------------------------------------------------

function Math#min(a: int, b: int): int;
axiom (forall a: int, b: int :: { Math#min(a, b) } a <= b <==> Math#min(a, b) == a);
axiom (forall a: int, b: int :: { Math#min(a, b) } b <= a <==> Math#min(a, b) == b);
axiom (forall a: int, b: int :: { Math#min(a, b) } Math#min(a, b) == a || Math#min(a, b) == b);

function Math#clip(a: int): int;
axiom (forall a: int :: { Math#clip(a) } 0 <= a ==> Math#clip(a) == a);
axiom (forall a: int :: { Math#clip(a) } a < 0  ==> Math#clip(a) == 0);

type MultiSet T = [T]int;

function $IsGoodMultiSet<T>(ms: MultiSet T): bool;
// ints are non-negative, used after havocing, and for conversion from sequences to multisets.
axiom (forall<T> ms: MultiSet T :: { $IsGoodMultiSet(ms) }
  $IsGoodMultiSet(ms) <==>
  (forall bx: T :: { ms[bx] } 0 <= ms[bx] && ms[bx] <= MultiSet#Card(ms)));

function MultiSet#Card<T>(MultiSet T): int;
axiom (forall<T> s: MultiSet T :: { MultiSet#Card(s) } 0 <= MultiSet#Card(s));
axiom (forall<T> s: MultiSet T, x: T, n: int :: { MultiSet#Card(s[x := n]) }
  0 <= n ==> MultiSet#Card(s[x := n]) == MultiSet#Card(s) - s[x] + n);

function MultiSet#Empty<T>(): MultiSet T;
axiom (forall<T> o: T :: { MultiSet#Empty()[o] } MultiSet#Empty()[o] == 0);
axiom (forall<T> s: MultiSet T :: { MultiSet#Card(s) }
  (MultiSet#Card(s) == 0 <==> s == MultiSet#Empty()) &&
  (MultiSet#Card(s) != 0 ==> (exists x: T :: 0 < s[x])));

function MultiSet#Singleton<T>(T): MultiSet T;
axiom (forall<T> r: T, o: T :: { MultiSet#Singleton(r)[o] } (MultiSet#Singleton(r)[o] == 1 <==> r == o) &&
                                                            (MultiSet#Singleton(r)[o] == 0 <==> r != o));
axiom (forall<T> r: T :: { MultiSet#Singleton(r) } MultiSet#Singleton(r) == MultiSet#UnionOne(MultiSet#Empty(), r));

function MultiSet#UnionOne<T>(MultiSet T, T): MultiSet T;
// pure containment axiom (in the original multiset or is the added element)
axiom (forall<T> a: MultiSet T, x: T, o: T :: { MultiSet#UnionOne(a,x)[o] }
  0 < MultiSet#UnionOne(a,x)[o] <==> o == x || 0 < a[o]);
// union-ing increases count by one
axiom (forall<T> a: MultiSet T, x: T :: { MultiSet#UnionOne(a, x) }
  MultiSet#UnionOne(a, x)[x] == a[x] + 1);
// non-decreasing
axiom (forall<T> a: MultiSet T, x: T, y: T :: { MultiSet#UnionOne(a, x), a[y] }
  0 < a[y] ==> 0 < MultiSet#UnionOne(a, x)[y]);
// other elements unchanged
axiom (forall<T> a: MultiSet T, x: T, y: T :: { MultiSet#UnionOne(a, x), a[y] }
  x != y ==> a[y] == MultiSet#UnionOne(a, x)[y]);
axiom (forall<T> a: MultiSet T, x: T :: { MultiSet#Card(MultiSet#UnionOne(a, x)) }
  MultiSet#Card(MultiSet#UnionOne(a, x)) == MultiSet#Card(a) + 1);


function MultiSet#Union<T>(MultiSet T, MultiSet T): MultiSet T;
// union-ing is the sum of the contents
axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Union(a,b)[o] }
  MultiSet#Union(a,b)[o] == a[o] + b[o]);
axiom (forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Card(MultiSet#Union(a,b)) }
  MultiSet#Card(MultiSet#Union(a,b)) == MultiSet#Card(a) + MultiSet#Card(b));

function MultiSet#Intersection<T>(MultiSet T, MultiSet T): MultiSet T;
axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Intersection(a,b)[o] }
  MultiSet#Intersection(a,b)[o] == Math#min(a[o],  b[o]));

// left and right pseudo-idempotence
axiom (forall<T> a, b: MultiSet T :: { MultiSet#Intersection(MultiSet#Intersection(a, b), b) }
  MultiSet#Intersection(MultiSet#Intersection(a, b), b) == MultiSet#Intersection(a, b));
axiom (forall<T> a, b: MultiSet T :: { MultiSet#Intersection(a, MultiSet#Intersection(a, b)) }
  MultiSet#Intersection(a, MultiSet#Intersection(a, b)) == MultiSet#Intersection(a, b));

// multiset difference, a - b. clip() makes it positive.
function MultiSet#Difference<T>(MultiSet T, MultiSet T): MultiSet T;
axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Difference(a,b)[o] }
  MultiSet#Difference(a,b)[o] == Math#clip(a[o] - b[o]));
axiom (forall<T> a, b: MultiSet T, y: T :: { MultiSet#Difference(a, b), b[y], a[y] }
  a[y] <= b[y] ==> MultiSet#Difference(a, b)[y] == 0 );
axiom (forall<T> a, b: MultiSet T ::
  { MultiSet#Card(MultiSet#Difference(a, b)) }
  MultiSet#Card(MultiSet#Difference(a, b)) + MultiSet#Card(MultiSet#Difference(b, a))
  + 2 * MultiSet#Card(MultiSet#Intersection(a, b))
    == MultiSet#Card(MultiSet#Union(a, b)) &&
  MultiSet#Card(MultiSet#Difference(a, b)) == MultiSet#Card(a) - MultiSet#Card(MultiSet#Intersection(a, b)));

// multiset subset means a must have at most as many of each element as b
function MultiSet#Subset<T>(MultiSet T, MultiSet T): bool;
axiom (forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Subset(a,b) }
  MultiSet#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <= b[o]));

function MultiSet#Equal<T>(MultiSet T, MultiSet T): bool;
axiom (forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Equal(a,b) }
  MultiSet#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] == b[o]));
// extensionality axiom for multisets
axiom (forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Equal(a,b) }
  MultiSet#Equal(a,b) ==> a == b);

function MultiSet#Disjoint<T>(MultiSet T, MultiSet T): bool;
axiom (forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Disjoint(a,b) }
  MultiSet#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] == 0 || b[o] == 0));

// conversion to a multiset. each element in the original set has duplicity 1.
function MultiSet#FromSet<T>(Set T): MultiSet T;
axiom (forall<T> s: Set T, a: T :: { MultiSet#FromSet(s)[a] }
  (MultiSet#FromSet(s)[a] == 0 <==> !s[a]) &&
  (MultiSet#FromSet(s)[a] == 1 <==> s[a]));
axiom (forall<T> s: Set T :: { MultiSet#Card(MultiSet#FromSet(s)) }
  MultiSet#Card(MultiSet#FromSet(s)) == Set#Card(s));

// conversion to a multiset, from a sequence.
function MultiSet#FromSeq<T>(Seq T): MultiSet T uses {
  axiom (forall<T> :: MultiSet#FromSeq(Seq#Empty(): Seq T) == MultiSet#Empty(): MultiSet T);
}
// conversion produces a good map.
axiom (forall<T> s: Seq T :: { MultiSet#FromSeq(s) } $IsGoodMultiSet(MultiSet#FromSeq(s)) );
// cardinality axiom
axiom (forall<T> s: Seq T ::
  { MultiSet#Card(MultiSet#FromSeq(s)) }
    MultiSet#Card(MultiSet#FromSeq(s)) == Seq#Length(s));
// building axiom
axiom (forall<T> s: Seq T, v: T ::
  { MultiSet#FromSeq(Seq#Build(s, v)) }
    MultiSet#FromSeq(Seq#Build(s, v)) == MultiSet#UnionOne(MultiSet#FromSeq(s), v)
  );

// concatenation axiom
axiom (forall<T> a: Seq T, b: Seq T ::
  { MultiSet#FromSeq(Seq#Append(a, b)) }
    MultiSet#FromSeq(Seq#Append(a, b)) == MultiSet#Union(MultiSet#FromSeq(a), MultiSet#FromSeq(b)) );

// update axiom
axiom (forall<T> s: Seq T, i: int, v: T, x: T ::
  { MultiSet#FromSeq(Seq#Update(s, i, v))[x] }
    0 <= i && i < Seq#Length(s) ==>
    MultiSet#FromSeq(Seq#Update(s, i, v))[x] ==
      MultiSet#Union(MultiSet#Difference(MultiSet#FromSeq(s), MultiSet#Singleton(Seq#Index(s,i))), MultiSet#Singleton(v))[x] );
  // i.e. MS(Update(s, i, v)) == MS(s) - {{s[i]}} + {{v}}
axiom (forall<T> s: Seq T, x: T :: { MultiSet#FromSeq(s)[x] }
  (exists i : int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && x == Seq#Index(s,i)) <==> 0 < MultiSet#FromSeq(s)[x] );

// ---------------------------------------------------------------
// -- Axiomatization of sequences --------------------------------
// ---------------------------------------------------------------

type Seq T;

function Seq#Length<T>(Seq T): int;
axiom (forall<T> s: Seq T :: { Seq#Length(s) } 0 <= Seq#Length(s));

function Seq#Empty<T>(): Seq T;
axiom (forall<T> :: { Seq#Empty(): Seq T } Seq#Length(Seq#Empty(): Seq T) == 0);
axiom (forall<T> s: Seq T :: { Seq#Length(s) }
  (Seq#Length(s) == 0 ==> s == Seq#Empty())
// The following would be a nice fact to include, because it would enable verifying the
// GenericPick.SeqPick* methods in Test/dafny0/SmallTests.dfy.  However, it substantially
// slows down performance on some other tests, including running seemingly forever on
// some.
//  && (Seq#Length(s) != 0 ==> (exists x: T :: Seq#Contains(s, x)))
  );

// The empty sequence $Is any type
//axiom (forall<T> t: Ty :: {$Is(Seq#Empty(): Seq T, TSeq(t))} $Is(Seq#Empty(): Seq T, TSeq(t)));

function Seq#Singleton<T>(T): Seq T;
axiom (forall<T> t: T :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);

function Seq#Build<T>(s: Seq T, val: T): Seq T;
function Seq#Build_inv0<T>(s: Seq T) : Seq T;
function Seq#Build_inv1<T>(s: Seq T) : T;
axiom (forall<T> s: Seq T, val: T ::
  { Seq#Build(s, val) }
  Seq#Build_inv0(Seq#Build(s, val)) == s &&
  Seq#Build_inv1(Seq#Build(s, val)) == val);

axiom (forall<T> s: Seq T, v: T ::
  { Seq#Build(s,v) }
  Seq#Length(Seq#Build(s,v)) == 1 + Seq#Length(s));
axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Index(Seq#Build(s,v), i) }
  (i == Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == v) &&
  (i != Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == Seq#Index(s, i)));

// Build preserves $Is
axiom (forall s: Seq Box, bx: Box, t: Ty :: { $Is(Seq#Build(s,bx),TSeq(t)) }
    $Is(s,TSeq(t)) && $IsBox(bx,t) ==> $Is(Seq#Build(s,bx),TSeq(t)));

function Seq#Create(ty: Ty, heap: Heap, len: int, init: HandleType): Seq Box;
axiom (forall ty: Ty, heap: Heap, len: int, init: HandleType ::
  { Seq#Length(Seq#Create(ty, heap, len, init): Seq Box) }
  $IsGoodHeap(heap) && 0 <= len ==>
  Seq#Length(Seq#Create(ty, heap, len, init): Seq Box) == len);
axiom (forall ty: Ty, heap: Heap, len: int, init: HandleType, i: int ::
  { Seq#Index(Seq#Create(ty, heap, len, init), i) }
  $IsGoodHeap(heap) && 0 <= i && i < len ==>
  Seq#Index(Seq#Create(ty, heap, len, init), i) == Apply1(TInt, ty, heap, init, $Box(i)));

function Seq#Append<T>(Seq T, Seq T): Seq T;
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Length(Seq#Append(s0,s1)) }
  Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));

function Seq#Index<T>(Seq T, int): T;
axiom (forall<T> t: T :: { Seq#Index(Seq#Singleton(t), 0) } Seq#Index(Seq#Singleton(t), 0) == t);
axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) }
  (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)) &&
  (Seq#Length(s0) <= n ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, n - Seq#Length(s0))));

function Seq#Update<T>(Seq T, int, T): Seq T;
axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Length(Seq#Update(s,i,v)) }
  0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s,i,v)) == Seq#Length(s));
axiom (forall<T> s: Seq T, i: int, v: T, n: int :: { Seq#Index(Seq#Update(s,i,v),n) }
  0 <= n && n < Seq#Length(s) ==>
    (i == n ==> Seq#Index(Seq#Update(s,i,v),n) == v) &&
    (i != n ==> Seq#Index(Seq#Update(s,i,v),n) == Seq#Index(s,n)));

function Seq#Contains<T>(Seq T, T): bool;
axiom (forall<T> s: Seq T, x: T :: { Seq#Contains(s,x) }
  Seq#Contains(s,x) <==>
    (exists i: int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && Seq#Index(s,i) == x));
axiom (forall<T> x: T ::
  { Seq#Contains(Seq#Empty(), x) }
  !Seq#Contains(Seq#Empty(), x));

axiom (forall<T> s0: Seq T, s1: Seq T, x: T ::
  { Seq#Contains(Seq#Append(s0, s1), x) }
  Seq#Contains(Seq#Append(s0, s1), x) <==>
    Seq#Contains(s0, x) || Seq#Contains(s1, x));

axiom (forall<T> s: Seq T, v: T, x: T ::  // needed to prove things like '4 in [2,3,4]', see method TestSequences0 in SmallTests.dfy
  { Seq#Contains(Seq#Build(s, v), x) }
    Seq#Contains(Seq#Build(s, v), x) <==> (v == x || Seq#Contains(s, x)));

axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Contains(Seq#Take(s, n), x) }
  Seq#Contains(Seq#Take(s, n), x) <==>
    (exists i: int :: { Seq#Index(s, i) }
      0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));
axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Contains(Seq#Drop(s, n), x) }
  Seq#Contains(Seq#Drop(s, n), x) <==>
    (exists i: int :: { Seq#Index(s, i) }
      0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

function Seq#Equal<T>(Seq T, Seq T): bool;
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
  Seq#Equal(s0,s1) <==>
    Seq#Length(s0) == Seq#Length(s1) &&
    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0,j) == Seq#Index(s1,j)));
axiom (forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a,b) }  // extensionality axiom for sequences
  Seq#Equal(a,b) ==> a == b);

function Seq#SameUntil<T>(Seq T, Seq T, int): bool;
axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#SameUntil(s0,s1,n) }
  Seq#SameUntil(s0,s1,n) <==>
    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        0 <= j && j < n ==> Seq#Index(s0,j) == Seq#Index(s1,j)));

function Seq#Take<T>(s: Seq T, howMany: int): Seq T;
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Take(s,n)) }
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n);
axiom (forall<T> s: Seq T, n: int, j: int ::
  {:weight 25}
  { Seq#Index(Seq#Take(s,n), j) }
  { Seq#Index(s, j), Seq#Take(s,n) }
  0 <= j && j < n && j < Seq#Length(s) ==>
    Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));

function Seq#Drop<T>(s: Seq T, howMany: int): Seq T;
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Drop(s,n)) }
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n);
axiom (forall<T> s: Seq T, n: int, j: int ::
  {:weight 25}
  { Seq#Index(Seq#Drop(s,n), j) }
  0 <= n && 0 <= j && j < Seq#Length(s)-n ==>
    Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, j+n));
axiom (forall<T> s: Seq T, n: int, k: int ::
  {:weight 25}
  { Seq#Index(s, k), Seq#Drop(s,n) }
  0 <= n && n <= k && k < Seq#Length(s) ==>
    Seq#Index(Seq#Drop(s,n), k-n) == Seq#Index(s, k));

axiom (forall<T> s, t: Seq T, n: int ::
  { Seq#Take(Seq#Append(s, t), n) }
  { Seq#Drop(Seq#Append(s, t), n) }
  n == Seq#Length(s)
  ==>
  Seq#Take(Seq#Append(s, t), n) == s &&
  Seq#Drop(Seq#Append(s, t), n) == t);

function Seq#FromArray(h: Heap, a: ref): Seq Box;
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
    { Seq#Index(Seq#FromArray(h, a): Seq Box, i) }
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
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
        { Seq#Take(Seq#Update(s, i, v), n) }
        0 <= i && i < n && n <= Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v) );
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
        { Seq#Take(Seq#Update(s, i, v), n) }
        n <= i && i < Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
        { Seq#Drop(Seq#Update(s, i, v), n) }
        0 <= n && n <= i && i < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i-n, v) );
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
        { Seq#Drop(Seq#Update(s, i, v), n) }
        0 <= i && i < n && n <= Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));
// Extension axiom, triggers only on Takes from arrays.
axiom (forall h: Heap, a: ref, n0, n1: int ::
        { Seq#Take(Seq#FromArray(h, a), n0), Seq#Take(Seq#FromArray(h, a), n1) }
        n0 + 1 == n1 && 0 <= n0 && n1 <= _System.array.Length(a) ==> Seq#Take(Seq#FromArray(h, a), n1) == Seq#Build(Seq#Take(Seq#FromArray(h, a), n0), read(h, a, IndexField(n0): Field Box)) );
// drop commutes with build.
axiom (forall<T> s: Seq T, v: T, n: int ::
        { Seq#Drop(Seq#Build(s, v), n) }
        0 <= n && n <= Seq#Length(s) ==> Seq#Drop(Seq#Build(s, v), n) == Seq#Build(Seq#Drop(s, n), v) );

function Seq#Rank<T>(Seq T): int;
axiom (forall s: Seq Box, i: int ::
        { DtRank($Unbox(Seq#Index(s, i)): DatatypeType) }
        0 <= i && i < Seq#Length(s) ==> DtRank($Unbox(Seq#Index(s, i)): DatatypeType) < Seq#Rank(s) );
axiom (forall<T> s: Seq T, i: int ::
        { Seq#Rank(Seq#Drop(s, i)) }
        0 < i && i <= Seq#Length(s) ==> Seq#Rank(Seq#Drop(s, i)) < Seq#Rank(s) );
axiom (forall<T> s: Seq T, i: int ::
        { Seq#Rank(Seq#Take(s, i)) }
        0 <= i && i < Seq#Length(s) ==> Seq#Rank(Seq#Take(s, i)) < Seq#Rank(s) );
axiom (forall<T> s: Seq T, i: int, j: int ::
        { Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) }
        0 <= i && i < j && j <= Seq#Length(s) ==> Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) < Seq#Rank(s) );

// Additional axioms about common things
axiom (forall<T> s: Seq T, n: int :: { Seq#Drop(s, n) }
        n == 0 ==> Seq#Drop(s, n) == s);
axiom (forall<T> s: Seq T, n: int :: { Seq#Take(s, n) }
        n == 0 ==> Seq#Take(s, n) == Seq#Empty());
axiom (forall<T> s: Seq T, m, n: int :: { Seq#Drop(Seq#Drop(s, m), n) }
        0 <= m && 0 <= n && m+n <= Seq#Length(s) ==>
        Seq#Drop(Seq#Drop(s, m), n) == Seq#Drop(s, m+n));

// ---------------------------------------------------------------
// -- Axiomatization of Maps -------------------------------------
// ---------------------------------------------------------------

type Map U V;

// A Map is defined by three functions, Map#Domain, Map#Elements, and #Map#Card.

function Map#Domain<U,V>(Map U V) : Set U;

function Map#Elements<U,V>(Map U V) : [U]V;

function Map#Card<U,V>(Map U V) : int;

axiom (forall<U,V> m: Map U V :: { Map#Card(m) } 0 <= Map#Card(m));

axiom (forall<U, V> m: Map U V ::
  { Map#Card(m) }
  Map#Card(m) == 0 <==> m == Map#Empty());

axiom (forall<U, V> m: Map U V ::
  { Map#Domain(m) }
  m == Map#Empty() || (exists k: U :: Map#Domain(m)[k]));
axiom (forall<U, V> m: Map U V ::
  { Map#Values(m) }
  m == Map#Empty() || (exists v: V :: Map#Values(m)[v]));
axiom (forall<U, V> m: Map U V ::
  { Map#Items(m) }
  m == Map#Empty() || (exists k, v: Box :: Map#Items(m)[$Box(#_System._tuple#2._#Make2(k, v))]));

axiom (forall<U, V> m: Map U V ::
  { Set#Card(Map#Domain(m)) }
  Set#Card(Map#Domain(m)) == Map#Card(m));
axiom (forall<U, V> m: Map U V ::
  { Set#Card(Map#Values(m)) }
  Set#Card(Map#Values(m)) <= Map#Card(m));
axiom (forall<U, V> m: Map U V ::
  { Set#Card(Map#Items(m)) }
  Set#Card(Map#Items(m)) == Map#Card(m));

// The set of Values of a Map can be obtained by the function Map#Values, which is
// defined as follows.  Remember, a Set is defined by membership (using Boogie's
// square brackets) and Map#Card, so we need to define what these mean for the Set
// returned by Map#Values.

function Map#Values<U,V>(Map U V) : Set V;

axiom (forall<U,V> m: Map U V, v: V :: { Map#Values(m)[v] }
  Map#Values(m)[v] ==
	(exists u: U :: { Map#Domain(m)[u] } { Map#Elements(m)[u] }
	  Map#Domain(m)[u] &&
    v == Map#Elements(m)[u]));

// The set of Items--that is, (key,value) pairs--of a Map can be obtained by the
// function Map#Items.  Again, we need to define membership of Set#Card for this
// set.  Everywhere else in this axiomatization, Map is parameterized by types U V,
// even though Dafny only ever instantiates U V with Box Box.  This makes the
// axiomatization more generic.  Function Map#Items, however, returns a set of
// pairs, and the axiomatization of pairs is Dafny specific.  Therefore, the
// definition of Map#Items here is to be considered Dafny specific.  Also, note
// that it relies on the two destructors for 2-tuples.

function Map#Items<U,V>(Map U V) : Set Box;

function #_System._tuple#2._#Make2(Box, Box) : DatatypeType;
function _System.Tuple2._0(DatatypeType) : Box;
function _System.Tuple2._1(DatatypeType) : Box;

axiom (forall m: Map Box Box, item: Box :: { Map#Items(m)[item] }
  Map#Items(m)[item] <==>
    Map#Domain(m)[_System.Tuple2._0($Unbox(item))] &&
    Map#Elements(m)[_System.Tuple2._0($Unbox(item))] == _System.Tuple2._1($Unbox(item)));

// Here are the operations that produce Map values.

function Map#Empty<U, V>(): Map U V;
axiom (forall<U, V> u: U ::
        { Map#Domain(Map#Empty(): Map U V)[u] }
        !Map#Domain(Map#Empty(): Map U V)[u]);

function Map#Glue<U, V>([U]bool, [U]V, Ty): Map U V;
axiom (forall<U, V> a: [U]bool, b: [U]V, t: Ty ::
  { Map#Domain(Map#Glue(a, b, t)) }
  Map#Domain(Map#Glue(a, b, t)) == a);
axiom (forall<U, V> a: [U]bool, b: [U]V, t: Ty ::
  { Map#Elements(Map#Glue(a, b, t)) }
  Map#Elements(Map#Glue(a, b, t)) == b);
axiom (forall a: [Box]bool, b: [Box]Box, t0, t1: Ty ::
  { Map#Glue(a, b, TMap(t0, t1)) }
  // In the following line, no trigger needed, since the quantifier only gets used in negative contexts
  (forall bx: Box :: a[bx] ==> $IsBox(bx, t0) && $IsBox(b[bx], t1))
  ==>
  $Is(Map#Glue(a, b, TMap(t0, t1)), TMap(t0, t1)));


//Build is used in displays, and for map updates
function Map#Build<U, V>(Map U V, U, V): Map U V;
/*axiom (forall<U, V> m: Map U V, u: U, v: V ::
  { Map#Domain(Map#Build(m, u, v))[u] } { Map#Elements(Map#Build(m, u, v))[u] }
  Map#Domain(Map#Build(m, u, v))[u] && Map#Elements(Map#Build(m, u, v))[u] == v);*/

axiom (forall<U, V> m: Map U V, u: U, u': U, v: V ::
  { Map#Domain(Map#Build(m, u, v))[u'] } { Map#Elements(Map#Build(m, u, v))[u'] }
  (u' == u ==> Map#Domain(Map#Build(m, u, v))[u'] &&
               Map#Elements(Map#Build(m, u, v))[u'] == v) &&
  (u' != u ==> Map#Domain(Map#Build(m, u, v))[u'] == Map#Domain(m)[u'] &&
               Map#Elements(Map#Build(m, u, v))[u'] == Map#Elements(m)[u']));
axiom (forall<U, V> m: Map U V, u: U, v: V :: { Map#Card(Map#Build(m, u, v)) }
  Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m));
axiom (forall<U, V> m: Map U V, u: U, v: V :: { Map#Card(Map#Build(m, u, v)) }
  !Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m) + 1);

// Map operations
function Map#Merge<U, V>(Map U V, Map U V): Map U V;
axiom (forall<U, V> m: Map U V, n: Map U V ::
  { Map#Domain(Map#Merge(m, n)) }
  Map#Domain(Map#Merge(m, n)) == Set#Union(Map#Domain(m), Map#Domain(n)));
axiom (forall<U, V> m: Map U V, n: Map U V, u: U ::
  { Map#Elements(Map#Merge(m, n))[u] }
  Map#Domain(Map#Merge(m, n))[u] ==>
    (!Map#Domain(n)[u] ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(m)[u]) &&
    (Map#Domain(n)[u] ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(n)[u]));

function Map#Subtract<U, V>(Map U V, Set U): Map U V;
axiom (forall<U, V> m: Map U V, s: Set U ::
  { Map#Domain(Map#Subtract(m, s)) }
  Map#Domain(Map#Subtract(m, s)) == Set#Difference(Map#Domain(m), s));
axiom (forall<U, V> m: Map U V, s: Set U, u: U ::
  { Map#Elements(Map#Subtract(m, s))[u] }
  Map#Domain(Map#Subtract(m, s))[u] ==>
    Map#Elements(Map#Subtract(m, s))[u] == Map#Elements(m)[u]);

//equality for maps
function Map#Equal<U, V>(Map U V, Map U V): bool;
axiom (forall<U, V> m: Map U V, m': Map U V::
  { Map#Equal(m, m') }
    Map#Equal(m, m') <==> (forall u : U :: Map#Domain(m)[u] == Map#Domain(m')[u]) &&
                          (forall u : U :: Map#Domain(m)[u] ==> Map#Elements(m)[u] == Map#Elements(m')[u]));
// extensionality
axiom (forall<U, V> m: Map U V, m': Map U V::
  { Map#Equal(m, m') }
    Map#Equal(m, m') ==> m == m');

function Map#Disjoint<U, V>(Map U V, Map U V): bool;
axiom (forall<U, V> m: Map U V, m': Map U V ::
  { Map#Disjoint(m, m') }
    Map#Disjoint(m, m') <==> (forall o: U :: {Map#Domain(m)[o]} {Map#Domain(m')[o]} !Map#Domain(m)[o] || !Map#Domain(m')[o]));

// ---------------------------------------------------------------
// -- Axiomatization of IMaps ------------------------------------
// ---------------------------------------------------------------

type IMap U V;

// A IMap is defined by two functions, Map#Domain and Map#Elements.

function IMap#Domain<U,V>(IMap U V) : Set U;

function IMap#Elements<U,V>(IMap U V) : [U]V;

axiom (forall<U, V> m: IMap U V ::
  { IMap#Domain(m) }
  m == IMap#Empty() || (exists k: U :: IMap#Domain(m)[k]));
axiom (forall<U, V> m: IMap U V ::
  { IMap#Values(m) }
  m == IMap#Empty() || (exists v: V :: IMap#Values(m)[v]));
axiom (forall<U, V> m: IMap U V ::
  { IMap#Items(m) }
  m == IMap#Empty() || (exists k, v: Box :: IMap#Items(m)[$Box(#_System._tuple#2._#Make2(k, v))]));

axiom (forall<U, V> m: IMap U V ::
  { IMap#Domain(m) }
  m == IMap#Empty() <==> IMap#Domain(m) == ISet#Empty());
axiom (forall<U, V> m: IMap U V ::
  { IMap#Values(m) }
  m == IMap#Empty() <==> IMap#Values(m) == ISet#Empty());
axiom (forall<U, V> m: IMap U V ::
  { IMap#Items(m) }
  m == IMap#Empty() <==> IMap#Items(m) == ISet#Empty());

// The set of Values of a IMap can be obtained by the function IMap#Values, which is
// defined as follows.  Remember, a ISet is defined by membership (using Boogie's
// square brackets) so we need to define what these mean for the Set
// returned by Map#Values.

function IMap#Values<U,V>(IMap U V) : Set V;

axiom (forall<U,V> m: IMap U V, v: V :: { IMap#Values(m)[v] }
  IMap#Values(m)[v] ==
	(exists u: U :: { IMap#Domain(m)[u] } { IMap#Elements(m)[u] }
	  IMap#Domain(m)[u] &&
    v == IMap#Elements(m)[u]));

// The set of Items--that is, (key,value) pairs--of a Map can be obtained by the
// function IMap#Items.
// Everywhere else in this axiomatization, IMap is parameterized by types U V,
// even though Dafny only ever instantiates U V with Box Box.  This makes the
// axiomatization more generic.  Function IMap#Items, however, returns a set of
// pairs, and the axiomatization of pairs is Dafny specific.  Therefore, the
// definition of IMap#Items here is to be considered Dafny specific.  Also, note
// that it relies on the two destructors for 2-tuples.

function IMap#Items<U,V>(IMap U V) : Set Box;

axiom (forall m: IMap Box Box, item: Box :: { IMap#Items(m)[item] }
  IMap#Items(m)[item] <==>
    IMap#Domain(m)[_System.Tuple2._0($Unbox(item))] &&
    IMap#Elements(m)[_System.Tuple2._0($Unbox(item))] == _System.Tuple2._1($Unbox(item)));

// Here are the operations that produce Map values.
function IMap#Empty<U, V>(): IMap U V;
axiom (forall<U, V> u: U ::
        { IMap#Domain(IMap#Empty(): IMap U V)[u] }
        !IMap#Domain(IMap#Empty(): IMap U V)[u]);

function IMap#Glue<U, V>([U] bool, [U]V, Ty): IMap U V;
axiom (forall<U, V> a: [U]bool, b: [U]V, t: Ty ::
  { IMap#Domain(IMap#Glue(a, b, t)) }
  IMap#Domain(IMap#Glue(a, b, t)) == a);
axiom (forall<U, V> a: [U]bool, b: [U]V, t: Ty ::
  { IMap#Elements(IMap#Glue(a, b, t)) }
  IMap#Elements(IMap#Glue(a, b, t)) == b);
axiom (forall a: [Box]bool, b: [Box]Box, t0, t1: Ty ::
  { IMap#Glue(a, b, TIMap(t0, t1)) }
  // In the following line, no trigger needed, since the quantifier only gets used in negative contexts
  (forall bx: Box :: a[bx] ==> $IsBox(bx, t0) && $IsBox(b[bx], t1))
  ==>
  $Is(Map#Glue(a, b, TIMap(t0, t1)), TIMap(t0, t1)));

//Build is used in displays
function IMap#Build<U, V>(IMap U V, U, V): IMap U V;
/*axiom (forall<U, V> m: IMap U V, u: U, v: V ::
  { IMap#Domain(IMap#Build(m, u, v))[u] } { IMap#Elements(IMap#Build(m, u, v))[u] }
  IMap#Domain(IMap#Build(m, u, v))[u] && IMap#Elements(IMap#Build(m, u, v))[u] == v);*/

axiom (forall<U, V> m: IMap U V, u: U, u': U, v: V ::
  { IMap#Domain(IMap#Build(m, u, v))[u'] } { IMap#Elements(IMap#Build(m, u, v))[u'] }
  (u' == u ==> IMap#Domain(IMap#Build(m, u, v))[u'] &&
               IMap#Elements(IMap#Build(m, u, v))[u'] == v) &&
  (u' != u ==> IMap#Domain(IMap#Build(m, u, v))[u'] == IMap#Domain(m)[u'] &&
               IMap#Elements(IMap#Build(m, u, v))[u'] == IMap#Elements(m)[u']));

//equality for imaps
function IMap#Equal<U, V>(IMap U V, IMap U V): bool;
axiom (forall<U, V> m: IMap U V, m': IMap U V::
  { IMap#Equal(m, m') }
    IMap#Equal(m, m') <==> (forall u : U :: IMap#Domain(m)[u] == IMap#Domain(m')[u]) &&
                          (forall u : U :: IMap#Domain(m)[u] ==> IMap#Elements(m)[u] == IMap#Elements(m')[u]));
// extensionality
axiom (forall<U, V> m: IMap U V, m': IMap U V::
  { IMap#Equal(m, m') }
    IMap#Equal(m, m') ==> m == m');

// IMap operations
function IMap#Merge<U, V>(IMap U V, IMap U V): IMap U V;
axiom (forall<U, V> m: IMap U V, n: IMap U V ::
  { IMap#Domain(IMap#Merge(m, n)) }
  IMap#Domain(IMap#Merge(m, n)) == Set#Union(IMap#Domain(m), IMap#Domain(n)));
axiom (forall<U, V> m: IMap U V, n: IMap U V, u: U ::
  { IMap#Elements(IMap#Merge(m, n))[u] }
  IMap#Domain(IMap#Merge(m, n))[u] ==>
    (!IMap#Domain(n)[u] ==> IMap#Elements(IMap#Merge(m, n))[u] == IMap#Elements(m)[u]) &&
    (IMap#Domain(n)[u] ==> IMap#Elements(IMap#Merge(m, n))[u] == IMap#Elements(n)[u]));

function IMap#Subtract<U, V>(IMap U V, Set U): IMap U V;
axiom (forall<U, V> m: IMap U V, s: Set U ::
  { IMap#Domain(IMap#Subtract(m, s)) }
  IMap#Domain(IMap#Subtract(m, s)) == Set#Difference(IMap#Domain(m), s));
axiom (forall<U, V> m: IMap U V, s: Set U, u: U ::
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
