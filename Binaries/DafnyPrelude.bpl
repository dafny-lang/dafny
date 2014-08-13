// Dafny prelude
// Created 9 February 2008 by Rustan Leino.
// Converted to Boogie 2 on 28 June 2008.
// Edited sequence axioms 20 October 2009 by Alex Summers.
// Modified 2014 by Dan Rosen.
// Copyright (c) 2008-2014, Microsoft.

const $$Language$Dafny: bool;  // To be recognizable to the ModelViewer as
axiom $$Language$Dafny;        // coming from a Dafny program.

// ---------------------------------------------------------------
// -- Types ------------------------------------------------------
// ---------------------------------------------------------------

type Ty;

const unique TBool : Ty;
const unique TInt  : Ty;
const unique TNat  : Ty;
const unique TReal : Ty;
function TSet(Ty)      : Ty;
function TMultiSet(Ty) : Ty;
function TSeq(Ty)      : Ty;
function TMap(Ty, Ty)  : Ty;

function Inv0_TSet(Ty) : Ty;
axiom (forall t: Ty :: { TSet(t) } Inv0_TSet(TSet(t)) == t);
function Inv0_TSeq(Ty) : Ty;
axiom (forall t: Ty :: { TSeq(t) } Inv0_TSeq(TSeq(t)) == t);
function Inv0_TMultiSet(Ty) : Ty;
axiom (forall t: Ty :: { TMultiSet(t) } Inv0_TMultiSet(TMultiSet(t)) == t);
function Inv0_TMap(Ty) : Ty;
function Inv1_TMap(Ty) : Ty;
axiom (forall t, u: Ty :: { TMap(t,u) } Inv0_TMap(TMap(t,u)) == t);
axiom (forall t, u: Ty :: { TMap(t,u) } Inv1_TMap(TMap(t,u)) == u);

// -- Classes and Datatypes --

// -- Type Tags --
type TyTag;
function Tag(Ty) : TyTag;

const unique TagBool     : TyTag;
const unique TagInt      : TyTag;
const unique TagNat      : TyTag;
const unique TagReal     : TyTag;
const unique TagSet      : TyTag;
const unique TagMultiSet : TyTag;
const unique TagSeq      : TyTag;
const unique TagMap      : TyTag;
const unique TagClass    : TyTag;

axiom Tag(TBool) == TagBool;
axiom Tag(TInt) == TagInt;
axiom Tag(TNat) == TagNat;
axiom Tag(TReal) == TagReal;
axiom (forall t: Ty    :: { TSet(t) }      Tag(TSet(t))      == TagSet);
axiom (forall t: Ty    :: { TMultiSet(t) } Tag(TMultiSet(t)) == TagMultiSet);
axiom (forall t: Ty    :: { TSeq(t) }      Tag(TSeq(t))      == TagSeq);
axiom (forall t, u: Ty :: { TMap(t,u) }    Tag(TMap(t,u))    == TagMap);

// ---------------------------------------------------------------
// -- Literals ---------------------------------------------------
// ---------------------------------------------------------------
function {:identity} LitInt(x: int): int { x }
axiom (forall x: int :: { $Box(LitInt(x)) } $Box(LitInt(x)) == Lit($Box(x)) );
function {:identity} LitReal(x: real): real { x }
axiom (forall x: real :: { $Box(LitReal(x)) } $Box(LitReal(x)) == Lit($Box(x)) );
function {:identity} Lit<T>(x: T): T { x }
axiom (forall<T> x: T :: { $Box(Lit(x)) } $Box(Lit(x)) == Lit($Box(x)) );

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

/*
axiom (forall<T> x: T :: { $Box(x) } $Unbox($Box(x)) == x);
axiom (forall b: Box :: { $Unbox(b): int } $Box($Unbox(b): int) == b);
axiom (forall b: Box :: { $Unbox(b): ref } $Box($Unbox(b): ref) == b);
axiom (forall b: Box :: { $Unbox(b): Set Box } $Box($Unbox(b): Set Box) == b);
axiom (forall b: Box :: { $Unbox(b): MultiSet Box } $Box($Unbox(b): MultiSet Box) == b);
axiom (forall b: Box :: { $Unbox(b): Seq Box } $Box($Unbox(b): Seq Box) == b);
axiom (forall b: Box :: { $Unbox(b): Map Box Box } $Box($Unbox(b): Map Box Box) == b);
axiom (forall b: Box :: { $Unbox(b): DatatypeType } $Box($Unbox(b): DatatypeType) == b);
// Note: an axiom like this for bool would not be sound; instead, we do:
function $IsCanonicalBoolBox(Box): bool;
axiom $IsCanonicalBoolBox($Box(false)) && $IsCanonicalBoolBox($Box(true));
axiom (forall b: Box :: { $Unbox(b): bool } $IsCanonicalBoolBox(b) ==> $Box($Unbox(b): bool) == b);
*/

axiom (forall<T> x : T :: { $Box(x) } $Unbox($Box(x)) == x);

axiom (forall bx : Box ::
    { $IsBox(bx, TInt) }
    ( $IsBox(bx, TInt) ==> $Box($Unbox(bx) : int) == bx && $Is($Unbox(bx) : int, TInt)));
axiom (forall bx : Box ::
    { $IsBox(bx, TNat) }
    ( $IsBox(bx, TNat) ==> $Box($Unbox(bx) : int) == bx && $Is($Unbox(bx) : int, TNat)));
axiom (forall bx : Box ::
    { $IsBox(bx, TReal) }
    ( $IsBox(bx, TReal) ==> $Box($Unbox(bx) : real) == bx && $Is($Unbox(bx) : real, TReal)));
axiom (forall bx : Box ::
    { $IsBox(bx, TBool) }
    ( $IsBox(bx, TBool) ==> $Box($Unbox(bx) : bool) == bx && $Is($Unbox(bx) : bool, TBool)));
axiom (forall bx : Box, t : Ty ::
    { $IsBox(bx, TSet(t)) }
    ( $IsBox(bx, TSet(t)) ==> $Box($Unbox(bx) : Set Box) == bx && $Is($Unbox(bx) : Set Box, TSet(t))));
axiom (forall bx : Box, t : Ty ::
    { $IsBox(bx, TMultiSet(t)) }
    ( $IsBox(bx, TMultiSet(t)) ==> $Box($Unbox(bx) : MultiSet Box) == bx && $Is($Unbox(bx) : MultiSet Box, TMultiSet(t))));
axiom (forall bx : Box, t : Ty ::
    { $IsBox(bx, TSeq(t)) }
    ( $IsBox(bx, TSeq(t)) ==> $Box($Unbox(bx) : Seq Box) == bx && $Is($Unbox(bx) : Seq Box, TSeq(t))));
axiom (forall bx : Box, s : Ty, t : Ty ::
    { $IsBox(bx, TMap(s, t)) }
    ( $IsBox(bx, TMap(s, t)) ==> $Box($Unbox(bx) : Map Box Box) == bx && $Is($Unbox(bx) : Map Box Box, TMap(s, t))));

axiom (forall<T> v : T, t : Ty ::
    { $IsBox($Box(v), t) }
    ( $IsBox($Box(v), t) <==> $Is(v,t) ));
axiom (forall<T> v : T, t : Ty, h : Heap ::
    { $IsAllocBox($Box(v), t, h) }
    ( $IsAllocBox($Box(v), t, h) <==> $IsAlloc(v,t,h) ));

// The following functions and axioms are used to obtain a $Box($Unbox(_)) wrapper around
// certain expressions.  Note that it assumes any booleans (or, indeed, values of any type) contained
// in the (multi)set are canonical (which is the case for any (multi)set that occurs in an execution of
// a Dafny program).
// The role of the parameter 'dummy' in the following is (an unfortunately clumsy construction
// whose only purpose is) simply to tell Boogie how to instantiate the type parameter 'T'.

/*
function $IsGoodSet_Extended<T>(s: Set Box, dummy: T): bool;
axiom (forall<T> ss: Set Box, dummy: T, bx: Box :: { $IsGoodSet_Extended(ss, dummy), ss[bx] }
  $IsGoodSet_Extended(ss, dummy) ==> ss[bx] ==> bx == $Box($Unbox(bx): T));
function $IsGoodMultiSet_Extended<T>(ms: MultiSet Box, dummy: T): bool;
axiom (forall<T> ms: MultiSet Box, dummy: T, bx: Box :: { $IsGoodMultiSet_Extended(ms, dummy), ms[bx] }
  $IsGoodMultiSet_Extended(ms, dummy) ==> 0 < ms[bx] ==> bx == $Box($Unbox(bx): T));
  */

// ---------------------------------------------------------------
// -- Is and IsAlloc ---------------------------------------------
// ---------------------------------------------------------------

// Type-argument to $Is is the /representation type/,
// the second value argument to $Is is the actual type.
function $Is<T>(T,Ty): bool;           // no heap for now
function $IsAlloc<T>(T,Ty,Heap): bool;

// Corresponding entries for boxes...
// This could probably be solved by having Box also inhabit Ty
function $IsBox<T>(T,Ty): bool;
function $IsAllocBox<T>(T,Ty,Heap): bool;

axiom(forall v : int  :: { $Is(v,TInt) }  $Is(v,TInt));
axiom(forall v : int  :: { $Is(v,TNat) }  $Is(v,TNat) <==> v >= 0);
axiom(forall v : real :: { $Is(v,TReal) } $Is(v,TReal));
axiom(forall v : bool :: { $Is(v,TBool) } $Is(v,TBool));

axiom(forall h : Heap, v : int  :: { $IsAlloc(v,TInt,h) }  $IsAlloc(v,TInt,h));
axiom(forall h : Heap, v : int  :: { $IsAlloc(v,TNat,h) }  $IsAlloc(v,TNat,h));
axiom(forall h : Heap, v : real :: { $IsAlloc(v,TReal,h) } $IsAlloc(v,TReal,h));
axiom(forall h : Heap, v : bool :: { $IsAlloc(v,TBool,h) } $IsAlloc(v,TBool,h));

axiom (forall v: Set Box, t0: Ty :: { $Is(v, TSet(t0)) }
  $Is(v, TSet(t0)) <==>
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
axiom (forall v: Set Box, t0: Ty, h: Heap :: { $IsAlloc(v, TSet(t0), h) }
  $IsAlloc(v, TSet(t0), h) <==>
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

axiom (forall v: Map Box Box, t0: Ty, t1: Ty ::
  { $Is(v, TMap(t0, t1)) }
  $Is(v, TMap(t0, t1))
     <==> (forall bx: Box ::
      { Map#Elements(v)[bx] } { Map#Domain(v)[bx] }
      Map#Domain(v)[bx] ==>
        $IsBox(Map#Elements(v)[bx], t1) &&
        $IsBox(bx, t0)));
axiom (forall v: Map Box Box, t0: Ty, t1: Ty, h: Heap ::
  { $IsAlloc(v, TMap(t0, t1), h) }
  $IsAlloc(v, TMap(t0, t1), h)
     <==> (forall bx: Box ::
      { Map#Elements(v)[bx] } { Map#Domain(v)[bx] }
      Map#Domain(v)[bx] ==>
        $IsAllocBox(Map#Elements(v)[bx], t1, h) &&
        $IsAllocBox(bx, t0, h)));

// ---------------------------------------------------------------
// -- Encoding of type names -------------------------------------
// ---------------------------------------------------------------

type ClassName;
const unique class._System.int: ClassName;
const unique class._System.bool: ClassName;
const unique class._System.set: ClassName;
const unique class._System.seq: ClassName;
const unique class._System.multiset: ClassName;

function /*{:never_pattern true}*/ dtype(ref): Ty; // changed from ClassName to Ty
// function /*{:never_pattern true}*/ TypeParams(ref, int): ClassName;

function TypeTuple(a: ClassName, b: ClassName): ClassName;
function TypeTupleCar(ClassName): ClassName;
function TypeTupleCdr(ClassName): ClassName;
// TypeTuple is injective in both arguments:
axiom (forall a: ClassName, b: ClassName :: { TypeTuple(a,b) }
  TypeTupleCar(TypeTuple(a,b)) == a &&
  TypeTupleCdr(TypeTuple(a,b)) == b);

// -- Function handles -------------------------------------------

type HandleType;

// ---------------------------------------------------------------
// -- Datatypes --------------------------------------------------
// ---------------------------------------------------------------

type DatatypeType;

// function /*{:never_pattern true}*/ DtType(DatatypeType): Ty;  // the analog of dtype for datatype values
                                                // changed from ClassName to Ty
// function /*{:never_pattern true}*/ DtTypeParams(DatatypeType, int): ClassName;  // the analog of TypeParams

type DtCtorId;
function DatatypeCtorId(DatatypeType): DtCtorId;

function DtRank(DatatypeType): int;
function BoxRank(Box): int;

axiom (forall d: DatatypeType :: {BoxRank($Box(d))} BoxRank($Box(d)) == DtRank(d));

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

function AtLayer<A>([LayerType]A, LayerType): A;
axiom (forall<A> f : [LayerType]A, ly : LayerType :: { AtLayer(f,ly) } AtLayer(f,ly) == f[ly]);
axiom (forall<A> f : [LayerType]A, ly : LayerType :: { AtLayer(f,$LS(ly)) } AtLayer(f,$LS(ly)) == AtLayer(f,ly));

// ---------------------------------------------------------------
// -- Fields -----------------------------------------------------
// ---------------------------------------------------------------

type Field alpha;

function FDim<T>(Field T): int;

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
function DeclName<T>(Field T): NameFamily;
function FieldOfDecl<alpha>(ClassName, NameFamily): Field alpha;
axiom (forall<T> cl : ClassName, nm: NameFamily ::
   {FieldOfDecl(cl, nm): Field T}
   DeclType(FieldOfDecl(cl, nm): Field T) == cl && DeclName(FieldOfDecl(cl, nm): Field T) == nm);

function $IsGhostField<T>(Field T): bool;

// ---------------------------------------------------------------
// -- Allocatedness and Heap Succession --------------------------
// ---------------------------------------------------------------


// $IsAlloc and $IsAllocBox are monotonic

axiom(forall<T> h, k : Heap, v : T, t : Ty ::
  { $HeapSucc(h, k), $IsAlloc(v, t, h) }
  $HeapSucc(h, k) ==> $IsAlloc(v, t, h) ==> $IsAlloc(v, t, k));
axiom(forall h, k : Heap, bx : Box, t : Ty ::
  { $HeapSucc(h, k), $IsAllocBox(bx, t, h) }
  $HeapSucc(h, k) ==> $IsAllocBox(bx, t, h) ==> $IsAllocBox(bx, t, k));

// No axioms for $Is and $IsBox since they don't talk about the heap.

const unique alloc: Field bool;
axiom FDim(alloc) == 0 && !$IsGhostField(alloc);  // treat as non-ghost field, because it cannot be changed by ghost code

// DtAlloc, removed
//function DtAlloc(DatatypeType, Heap): bool;
//axiom (forall h, k: Heap, d: DatatypeType ::
//  { $HeapSucc(h, k), DtAlloc(d, h) }
//  $HeapSucc(h, k) ==> DtAlloc(d, h) ==> DtAlloc(d, k));

// GenericAlloc removed.

/*
function GenericAlloc(Box, Heap): bool;
axiom (forall h: Heap, k: Heap, d: Box ::
  { $HeapSucc(h, k), GenericAlloc(d, h) }
  $HeapSucc(h, k) ==> GenericAlloc(d, h) ==> GenericAlloc(d, k));
// GenericAlloc ==>
//references
axiom (forall b: Box, h: Heap ::
  { GenericAlloc(b, h), h[$Unbox(b): ref, alloc] }
  GenericAlloc(b, h) ==>
  $Unbox(b): ref == null || h[$Unbox(b): ref, alloc]);
//seqs
axiom (forall b: Box, h: Heap, i: int ::
  { GenericAlloc(b, h), Seq#Index($Unbox(b): Seq Box, i) }
  GenericAlloc(b, h) &&
  0 <= i && i < Seq#Length($Unbox(b): Seq Box) ==>
  GenericAlloc( Seq#Index($Unbox(b): Seq Box, i), h ) );

//maps
//seq-like axiom, talking about the range elements
axiom (forall b: Box, h: Heap, i: Box ::
  { GenericAlloc(b, h), Map#Domain($Unbox(b): Map Box Box)[i] }
  GenericAlloc(b, h) && Map#Domain($Unbox(b): Map Box Box)[i] ==>
  GenericAlloc( Map#Elements($Unbox(b): Map Box Box)[i], h ) );
//set-like axiom, talking about the domain elements
axiom (forall b: Box, h: Heap, t: Box ::
  { GenericAlloc(b, h), Map#Domain($Unbox(b): Map Box Box)[t] }
  GenericAlloc(b, h) && Map#Domain($Unbox(b): Map Box Box)[t] ==>
  GenericAlloc(t, h));

//sets
axiom (forall b: Box, h: Heap, t: Box ::
  { GenericAlloc(b, h), ($Unbox(b): Set Box)[t] }
  GenericAlloc(b, h) && ($Unbox(b): Set Box)[t] ==>
  GenericAlloc(t, h));
//datatypes
axiom (forall b: Box, h: Heap ::
  { GenericAlloc(b, h), DtAlloc($Unbox(b): DatatypeType, h) }
  GenericAlloc(b, h) <==> DtAlloc($Unbox(b): DatatypeType, h));
axiom (forall dt: DatatypeType, h: Heap ::
  { GenericAlloc($Box(dt), h) }
  GenericAlloc($Box(dt), h) <==> DtAlloc(dt, h));
// ==> GenericAlloc
axiom (forall b: bool, h: Heap ::
  $IsGoodHeap(h) ==> GenericAlloc($Box(b), h));
axiom (forall x: int, h: Heap ::
  $IsGoodHeap(h) ==> GenericAlloc($Box(x), h));
axiom (forall r: ref, h: Heap ::
  { GenericAlloc($Box(r), h) }
  $IsGoodHeap(h) && (r == null || h[r,alloc]) ==> GenericAlloc($Box(r), h));
// boxes in the heap
axiom (forall r: ref, f: Field Box, h: Heap ::
  { GenericAlloc(read(h, r, f), h) }
  $IsGoodHeap(h) && r != null && read(h, r, alloc) ==>
  GenericAlloc(read(h, r, f), h));

axiom (forall h: Heap, r: ref, j: int ::
 { read(h, r, IndexField(j)) }
 $IsGoodHeap(h) && r != null && read(h, r, alloc) &&
 0 <= j && j < _System.array.Length(r)
 ==>
 GenericAlloc(read(h, r, IndexField(j)), h));
axiom (forall h: Heap, r: ref, m: Field Box, j: int ::
 { read(h, r, MultiIndexField(m, j)) }
 $IsGoodHeap(h) && r != null && read(h, r, alloc)
 // It would be best also to constrain MultiIndexField(m,j) to produce
 // a proper field (that is, to refer to an array element within
 // bounds.  However, since the LengthX fields of multi-dimentional
 // are produced on the fly, adding them would require more work.
 // Thus, the model to keep in mind is that MultiIndexField then
 // produces a field who value, when dereferenced for array 'r',
 // is a box that has the desired allocation properties.
 ==>
 GenericAlloc(read(h, r, MultiIndexField(m, j)), h));
 */


// ---------------------------------------------------------------
// -- Arrays -----------------------------------------------------
// ---------------------------------------------------------------

function _System.array.Length(a: ref): int;
axiom (forall o: ref :: 0 <= _System.array.Length(o));

// ---------------------------------------------------------------
// -- Reals ------------------------------------------------------
// ---------------------------------------------------------------

function _System.Real.RealToInt(h: Heap, x: real): int { int(x) }
function _System.Real.IntToReal(h: Heap, x: int): real { real(x) }

// ---------------------------------------------------------------
// -- The heap ---------------------------------------------------
// ---------------------------------------------------------------

type Heap = <alpha>[ref,Field alpha]alpha;
function {:inline true} read<alpha>(H:Heap, r:ref, f:Field alpha): alpha { H[r, f] }
function {:inline true} update<alpha>(H:Heap, r:ref, f:Field alpha, v:alpha): Heap { H[r,f := v] }

function $IsGoodHeap(Heap): bool;
var $Heap: Heap where $IsGoodHeap($Heap);

function $HeapSucc(Heap, Heap): bool;
axiom (forall<alpha> h: Heap, r: ref, f: Field alpha, x: alpha :: { update(h, r, f, x) }
  $IsGoodHeap(update(h, r, f, x)) ==>
  $HeapSucc(h, update(h, r, f, x)));
axiom (forall a,b,c: Heap :: { $HeapSucc(a,b), $HeapSucc(b,c) }
  $HeapSucc(a,b) && $HeapSucc(b,c) ==> $HeapSucc(a,c));
axiom (forall h: Heap, k: Heap :: { $HeapSucc(h,k) }
  $HeapSucc(h,k) ==> (forall o: ref :: { read(k, o, alloc) } read(h, o, alloc) ==> read(k, o, alloc)));

function $HeapSuccGhost(Heap, Heap): bool;
axiom (forall h: Heap, k: Heap :: { $HeapSuccGhost(h,k) }
  $HeapSuccGhost(h,k) ==>
    $HeapSucc(h,k) &&
    (forall<alpha> o: ref, f: Field alpha :: { read(k, o, f) }
      !$IsGhostField(f) ==> read(h, o, f) == read(k, o, f)));

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

// the singleton set will be the same type as its box
//axiom (forall bx : Ty, t: Ty :: { $Is(Set#Singleton(


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
axiom(forall<T> a: Set T, b: Set T :: { Set#Subset(a,b) }
  Set#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] ==> b[o]));
// axiom(forall<T> a: Set T, b: Set T ::
//   { Set#Subset(a,b), Set#Card(a), Set#Card(b) }  // very restrictive trigger
//   Set#Subset(a,b) ==> Set#Card(a) <= Set#Card(b));


function Set#Equal<T>(Set T, Set T): bool;
axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }
  Set#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <==> b[o]));
axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }  // extensionality axiom for sets
  Set#Equal(a,b) ==> a == b);

function Set#Disjoint<T>(Set T, Set T): bool;
axiom (forall<T> a: Set T, b: Set T :: { Set#Disjoint(a,b) }
  Set#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} !a[o] || !b[o]));

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
axiom(forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Subset(a,b) }
  MultiSet#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <= b[o]));

function MultiSet#Equal<T>(MultiSet T, MultiSet T): bool;
axiom(forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Equal(a,b) }
  MultiSet#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] == b[o]));
// extensionality axiom for multisets
axiom(forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Equal(a,b) }
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
function MultiSet#FromSeq<T>(Seq T): MultiSet T;
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
axiom (forall<T> :: MultiSet#FromSeq(Seq#Empty(): Seq T) == MultiSet#Empty(): MultiSet T);

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
axiom (forall<T> :: Seq#Length(Seq#Empty(): Seq T) == 0);
axiom (forall<T> s: Seq T :: { Seq#Length(s) } Seq#Length(s) == 0 ==> s == Seq#Empty());

// The empty sequence $Is any type
axiom (forall<T> t: Ty :: {$Is(Seq#Empty(): Seq T, t)} $Is(Seq#Empty(): Seq T, t));

function Seq#Singleton<T>(T): Seq T;
axiom (forall<T> t: T :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);

function Seq#Build<T>(s: Seq T, val: T): Seq T;
axiom (forall<T> s: Seq T, v: T :: { Seq#Length(Seq#Build(s,v)) }
  Seq#Length(Seq#Build(s,v)) == 1 + Seq#Length(s));
axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Index(Seq#Build(s,v), i) }
  (i == Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == v) &&
  (i != Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == Seq#Index(s, i)));

// Build preserves $Is
axiom (forall s: Seq Box, bx: Box, t: Ty :: { $Is(Seq#Build(s,bx),TSeq(t)) }
    $Is(s,TSeq(t)) && $IsBox(bx,t) ==> $Is(Seq#Build(s,bx),TSeq(t)));

function Seq#Append<T>(Seq T, Seq T): Seq T;
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Length(Seq#Append(s0,s1)) }
  Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));

// Append preserves $Is
axiom (forall s0 : Seq Box, s1 : Seq Box, t : Ty :: { $Is(Seq#Append(s0,s1),t) }
    $Is(s0,t) && $Is(s1,t) ==> $Is(Seq#Append(s0,s1),t));

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
axiom (forall x: ref ::
  { Seq#Contains(Seq#Empty(), x) }
  !Seq#Contains(Seq#Empty(), x));
axiom (forall<T> s0: Seq T, s1: Seq T, x: T ::
  { Seq#Contains(Seq#Append(s0, s1), x) }
  Seq#Contains(Seq#Append(s0, s1), x) <==>
    Seq#Contains(s0, x) || Seq#Contains(s1, x));

axiom (forall<T> s: Seq T, v: T, x: T ::
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
  0 <= n ==>
    (n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n) &&
    (Seq#Length(s) < n ==> Seq#Length(Seq#Take(s,n)) == Seq#Length(s)));
axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Take(s,n), j) } {:weight 25}
  0 <= j && j < n && j < Seq#Length(s) ==>
    Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));

function Seq#Drop<T>(s: Seq T, howMany: int): Seq T;
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Drop(s,n)) }
  0 <= n ==>
    (n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n) &&
    (Seq#Length(s) < n ==> Seq#Length(Seq#Drop(s,n)) == 0));
axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Drop(s,n), j) } {:weight 25}
  0 <= n && 0 <= j && j < Seq#Length(s)-n ==>
    Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, j+n));

axiom (forall<T> s, t: Seq T ::
  { Seq#Append(s, t) }
  Seq#Take(Seq#Append(s, t), Seq#Length(s)) == s &&
  Seq#Drop(Seq#Append(s, t), Seq#Length(s)) == t);

function Seq#FromArray(h: Heap, a: ref): Seq Box;
axiom (forall h: Heap, a: ref ::
  { Seq#Length(Seq#FromArray(h,a)) }
  /*
<<<<<<< local
    Seq#Length(Seq#FromArray(h, a)) == _System.array.Length(a));
axiom (forall h: Heap, a: ref :: { Seq#FromArray(h,a): Seq Box }
   (forall i: int :: 0 <= i && i < Seq#Length(Seq#FromArray(h, a)) ==> Seq#Index(Seq#FromArray(h, a), i) == read(h, a, IndexField(i))));
axiom (forall<alpha> h: Heap, o: ref, f: Field alpha, v: alpha, a: ref ::
  { Seq#FromArray(update(h, o, f, v), a) }
    o != a ==> Seq#FromArray(update(h, o, f, v), a) == Seq#FromArray(h, a) );
axiom (forall h: Heap, i: int, v: Box, a: ref ::
=======
*/
  Seq#Length(Seq#FromArray(h, a)) == _System.array.Length(a));
axiom (forall h: Heap, a: ref, i: int ::
  { Seq#Index(Seq#FromArray(h, a): Seq Box, i) }
  0 <= i && i < Seq#Length(Seq#FromArray(h, a)) ==> Seq#Index(Seq#FromArray(h, a), i) == read(h, a, IndexField(i)));
axiom (forall h0, h1: Heap, a: ref ::
  { Seq#FromArray(h1, a), $HeapSucc(h0, h1) }
  $IsGoodHeap(h0) && $IsGoodHeap(h1) && $HeapSucc(h0, h1) &&
  (forall i: int ::
    0 <= i && i < _System.array.Length(a) ==> read(h0, a, IndexField(i)) == read(h1, a, IndexField(i)))
  ==>
  Seq#FromArray(h0, a) == Seq#FromArray(h1, a));
axiom (forall h: Heap, i: int, v: Box, a: ref ::
  { Seq#FromArray(update(h, a, IndexField(i), v), a) }
    0 <= i && i < _System.array.Length(a) ==> Seq#FromArray(update(h, a, IndexField(i), v), a) == Seq#Update(Seq#FromArray(h, a), i, v) );
/**** Someday:
axiom (forall h: Heap, a: ref :: { Seq#FromArray(h, a) }
    $IsGoodHeap(h) &&
    a != null && read(h, a, alloc) && dtype(a) == class._System.array && TypeParams(a, 0) == class._System.bool
    ==>
    (forall i: int :: { Seq#Index(Seq#FromArray(h, a), i) }
      0 <= i && i < Seq#Length(Seq#FromArray(h, a)) ==>  $IsCanonicalBoolBox(Seq#Index(Seq#FromArray(h, a), i))));
****/

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
        0 <= i && i < n && n < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));
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

function Map#Domain<U, V>(Map U V): [U] bool;
function Map#Elements<U, V>(Map U V): [U]V;

function Map#Card<U, V>(Map U V): int;
axiom (forall<U, V> m: Map U V :: { Map#Card(m) } 0 <= Map#Card(m));

function Map#Empty<U, V>(): Map U V;
axiom (forall<U, V> u: U ::
        { Map#Domain(Map#Empty(): Map U V)[u] }
        !Map#Domain(Map#Empty(): Map U V)[u]);
axiom (forall<U, V> m: Map U V :: { Map#Card(m) } Map#Card(m) == 0 <==> m == Map#Empty());

function Map#Glue<U, V>([U] bool, [U]V): Map U V;
axiom (forall<U, V> a: [U] bool, b:[U]V ::
        { Map#Domain(Map#Glue(a, b)) }
        Map#Domain(Map#Glue(a, b)) == a);
axiom (forall<U, V> a: [U] bool, b:[U]V ::
        { Map#Elements(Map#Glue(a, b)) }
        Map#Elements(Map#Glue(a, b)) == b);


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

