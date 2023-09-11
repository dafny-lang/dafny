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

function Inv0_TBitvector(Ty) : int;

// There are further type functions and axioms in the preludes of collection types.

// -- Classes and Datatypes --

// -- Type Tags --
type TyTag;
function Tag(Ty) : TyTag;

const unique TagBool     : TyTag;
const unique TagChar     : TyTag;
const unique TagInt      : TyTag;
const unique TagReal     : TyTag;
const unique TagORDINAL  : TyTag;
// There are further tags in the preludes of collection types.

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
axiom (forall<T> x : T :: { $Box(x) } $Unbox($Box(x)) == x);

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
    ( $IsBox(bx, TBitvector(0)) ==> $Box($Unbox(bx) : Bv0) == bx && $Is($Unbox(bx) : Bv0, TBitvector(0))));

axiom (forall<T> v : T, t : Ty ::
    { $IsBox($Box(v), t) }
    ( $IsBox($Box(v), t) <==> $Is(v,t) ));
axiom (forall<T> v : T, t : Ty, h : Heap ::
    { $IsAllocBox($Box(v), t, h) }
    ( $IsAllocBox($Box(v), t, h) <==> $IsAlloc(v,t,h) ));

// There are further box/unbox axioms in the preludes of collection types.

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

function $IsAlloc<T>(T,Ty,Heap): bool;
axiom(forall h : Heap, v : int  :: { $IsAlloc(v,TInt,h) }  $IsAlloc(v,TInt,h));
axiom(forall h : Heap, v : real :: { $IsAlloc(v,TReal,h) } $IsAlloc(v,TReal,h));
axiom(forall h : Heap, v : bool :: { $IsAlloc(v,TBool,h) } $IsAlloc(v,TBool,h));
axiom(forall h : Heap, v : char :: { $IsAlloc(v,TChar,h) } $IsAlloc(v,TChar,h));
axiom(forall h : Heap, v : ORDINAL :: { $IsAlloc(v,TORDINAL,h) } $IsAlloc(v,TORDINAL,h));
    
axiom (forall v: Bv0, h: Heap :: { $IsAlloc(v, TBitvector(0), h) } $IsAlloc(v, TBitvector(0), h));

// There are further Is and IsAlloc axioms in the preludes of collection types.

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
}
axiom (forall h: Heap, k: Heap :: { $HeapSuccGhost(h,k) }
  $HeapSuccGhost(h,k) ==>
    $HeapSucc(h,k) &&
    (forall<alpha> o: ref, f: Field alpha :: { read(k, o, f) }
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

const unique alloc: Field bool;
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
type Heap = [ref]<alpha>[Field alpha]Box;
function {:inline} read<alpha>(H: Heap, r: ref, f: Field alpha) : alpha { $Unbox(H[r][f]) }
function {:inline} update<alpha>(H:Heap, r:ref, f:Field alpha, v:alpha): Heap { H[r := H[r][f := $Box(v)]] }

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
// -- Useful macros ----------------------------------------------
// ---------------------------------------------------------------

// havoc everything in $Heap, except {this}+rds+nw
procedure $YieldHavoc(this: ref, rds: Set, nw: Set);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha :: { read($Heap, $o, $f) }
            $o != null && read(old($Heap), $o, alloc) ==>
            $o == this || rds[$Box($o)] || nw[$Box($o)] ==>
              read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);

// havoc everything in $Heap, except rds-modi-{this}
procedure $IterHavoc0(this: ref, rds: Set, modi: Set);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha :: { read($Heap, $o, $f) }
            $o != null && read(old($Heap), $o, alloc) ==>
            rds[$Box($o)] && !modi[$Box($o)] && $o != this ==>
              read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);

// havoc $Heap at {this}+modi+nw
procedure $IterHavoc1(this: ref, modi: Set, nw: Set);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha :: { read($Heap, $o, $f) }
            $o != null && read(old($Heap), $o, alloc) ==>
              read($Heap, $o, $f) == read(old($Heap), $o, $f) ||
              $o == this || modi[$Box($o)] || nw[$Box($o)]);
  ensures $HeapSucc(old($Heap), $Heap);

procedure $IterCollectNewObjects(prevHeap: Heap, newHeap: Heap, this: ref, NW: Field (Set))
                        returns (s: Set);
  ensures (forall bx: Box :: { s[bx] } s[bx] <==>
              (read(newHeap, this, NW) : Set)[bx] ||
              ($Unbox(bx) != null && !read(prevHeap, $Unbox(bx):ref, alloc) && read(newHeap, $Unbox(bx):ref, alloc)));

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
