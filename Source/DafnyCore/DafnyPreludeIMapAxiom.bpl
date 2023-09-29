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

function TIMap(Ty, Ty) : Ty;
function Inv0_TIMap(Ty) : Ty;
function Inv1_TIMap(Ty) : Ty;
axiom (forall t, u: Ty :: { TIMap(t,u) } Inv0_TIMap(TIMap(t,u)) == t);
axiom (forall t, u: Ty :: { TIMap(t,u) } Inv1_TIMap(TIMap(t,u)) == u);
axiom (forall t, u: Ty :: { TIMap(t,u) } Tag(TIMap(t,u)) == TagIMap);

const unique TagIMap     : TyTag;

// ---------------------------------------------------------------
// -- Is and IsAlloc ---------------------------------------------
// ---------------------------------------------------------------

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

axiom (forall v: IMap, t0: Ty, t1: Ty, h: Heap ::
  { $IsAlloc(v, TIMap(t0, t1), h) }
  $IsAlloc(v, TIMap(t0, t1), h)
     <==> (forall bx: Box ::
      { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] }
      IMap#Domain(v)[bx] ==>
        $IsAllocBox(IMap#Elements(v)[bx], t1, h) &&
        $IsAllocBox(bx, t0, h)));

// ---------------------------------------------------------------
// -- Boxing and unboxing ----------------------------------------
// ---------------------------------------------------------------

axiom (forall bx : Box, s : Ty, t : Ty ::
    { $IsBox(bx, TIMap(s, t)) }
    ( $IsBox(bx, TIMap(s, t)) ==> $Box($Unbox(bx) : IMap) == bx && $Is($Unbox(bx) : IMap, TIMap(s, t))));

// ---------------------------------------------------------------
// -- Axiomatization of IMaps ------------------------------------
// ---------------------------------------------------------------

type IMap;

// A IMap is defined by two functions, Map#Domain and Map#Elements.

function IMap#Domain(IMap) : Set;

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

// The set of Values of a IMap can be obtained by the function IMap#Values, which is
// defined as follows.  Remember, a ISet is defined by membership (using Boogie's
// square brackets) so we need to define what these mean for the Set
// returned by Map#Values.

function IMap#Values(IMap) : Set;

axiom (forall m: IMap, v: Box :: { IMap#Values(m)[v] }
  IMap#Values(m)[v] ==
	(exists u: Box :: { IMap#Domain(m)[u] } { IMap#Elements(m)[u] }
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

function IMap#Items(IMap) : Set;

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
  $Is(Map#Glue(a, b, TIMap(t0, t1)), TIMap(t0, t1)));

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
  IMap#Domain(IMap#Merge(m, n)) == Set#Union(IMap#Domain(m), IMap#Domain(n)));
axiom (forall m: IMap, n: IMap, u: Box ::
  { IMap#Elements(IMap#Merge(m, n))[u] }
  IMap#Domain(IMap#Merge(m, n))[u] ==>
    (!IMap#Domain(n)[u] ==> IMap#Elements(IMap#Merge(m, n))[u] == IMap#Elements(m)[u]) &&
    (IMap#Domain(n)[u] ==> IMap#Elements(IMap#Merge(m, n))[u] == IMap#Elements(n)[u]));

function IMap#Subtract(IMap, Set): IMap;
axiom (forall m: IMap, s: Set ::
  { IMap#Domain(IMap#Subtract(m, s)) }
  IMap#Domain(IMap#Subtract(m, s)) == Set#Difference(IMap#Domain(m), s));
axiom (forall m: IMap, s: Set, u: Box ::
  { IMap#Elements(IMap#Subtract(m, s))[u] }
  IMap#Domain(IMap#Subtract(m, s))[u] ==>
    IMap#Elements(IMap#Subtract(m, s))[u] == IMap#Elements(m)[u]);
