// Dafny prelude
// Created 9 February 2008 by Rustan Leino.
// Converted to Boogie 2 on 28 June 2008.
// Copyright (c) 2008, Microsoft.

type ref;
const null: ref;

// ---------------------------------------------------------------
// -- Axiomatization of sets -------------------------------------
// ---------------------------------------------------------------

type Set T = [T]bool;

function Set#Empty<T>() returns (Set T);
axiom (forall<T> o: T :: { Set#Empty()[o] } !Set#Empty()[o]);

function Set#Singleton<T>(T) returns (Set T);
axiom (forall<T> r: T :: { Set#Singleton(r) } Set#Singleton(r)[r]);
axiom (forall<T> r: T, o: T :: { Set#Singleton(r)[o] } Set#Singleton(r)[o] <==> r == o);

function Set#UnionOne<T>(Set T, T) returns (Set T);
axiom (forall<T> a: Set T, x: T, o: T :: { Set#UnionOne(a,x)[o] }
  Set#UnionOne(a,x)[o] <==> o == x || a[o]);

function Set#Union<T>(Set T, Set T) returns (Set T);
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Union(a,b)[o] }
  Set#Union(a,b)[o] <==> a[o] || b[o]);

function Set#Intersection<T>(Set T, Set T) returns (Set T);
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Intersection(a,b)[o] }
  Set#Intersection(a,b)[o] <==> a[o] && b[o]);

function Set#Difference<T>(Set T, Set T) returns (Set T);
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Difference(a,b)[o] }
  Set#Difference(a,b)[o] <==> a[o] && !b[o]);

function Set#Subset<T>(Set T, Set T) returns (bool);
axiom(forall<T> a: Set T, b: Set T :: { Set#Subset(a,b) }
  Set#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] ==> b[o]));

function Set#Equal<T>(Set T, Set T) returns (bool);
axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }
  Set#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <==> b[o]));
axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }  // extensionality axiom for sets
  Set#Equal(a,b) ==> a == b);

function Set#Disjoint<T>(Set T, Set T) returns (bool);
axiom (forall<T> a: Set T, b: Set T :: { Set#Disjoint(a,b) }
  Set#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} !a[o] || !b[o]));

// ---------------------------------------------------------------
// -- Axiomatization of sequences --------------------------------
// ---------------------------------------------------------------

type Seq T;

function Seq#Length<T>(Seq T) returns (int);
axiom (forall<T> s: Seq T :: { Seq#Length(s) } 0 <= Seq#Length(s));

function Seq#Empty<T>() returns (Seq T);
axiom (forall<T> :: Seq#Length(Seq#Empty(): Seq T) == 0);
axiom (forall<T> s: Seq T :: { Seq#Length(s) } Seq#Length(s) == 0 ==> s == Seq#Empty());

function Seq#Singleton<T>(T) returns (Seq T);
axiom (forall<T> t: T :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);

function Seq#Build<T>(s: Seq T, index: int, val: T, newLength: int) returns (Seq T);
axiom (forall<T> s: Seq T, i: int, v: T, len: int :: { Seq#Length(Seq#Build(s,i,v,len)) }
  Seq#Length(Seq#Build(s,i,v,len)) == len);

function Seq#Append<T>(Seq T, Seq T) returns (Seq T);
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Length(Seq#Append(s0,s1)) }
  Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));

function Seq#Index<T>(Seq T, int) returns (T);
axiom (forall<T> t: T :: { Seq#Index(Seq#Singleton(t), 0) } Seq#Index(Seq#Singleton(t), 0) == t);
axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) }
  (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)) &&
  (Seq#Length(s0) <= n ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, n - Seq#Length(s0))));
axiom (forall<T> s: Seq T, i: int, v: T, len: int, n: int :: { Seq#Index(Seq#Build(s,i,v,len),n) }
  (i == n ==> Seq#Index(Seq#Build(s,i,v,len),n) == v) &&
  (i != n ==> Seq#Index(Seq#Build(s,i,v,len),n) == Seq#Index(s,n)));

function Seq#Contains<T>(Seq T, T) returns (bool);
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
axiom (forall<T> s: Seq T, i: int, v: T, len: int, x: T ::
  { Seq#Contains(Seq#Build(s, i, v, len), x) }
  Seq#Contains(Seq#Build(s, i, v, len), x) <==>
    x == v || Seq#Contains(s, x));
axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Contains(Seq#Take(s, n), x) }
  Seq#Contains(Seq#Take(s, n), x) <==>
    (exists i: int :: { Seq#Index(s, i) }
      0 <= i && i < n && n <= Seq#Length(s) && Seq#Index(s, i) == x));
axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Contains(Seq#Drop(s, n), x) }
  Seq#Contains(Seq#Drop(s, n), x) <==>
    (exists i: int :: { Seq#Index(s, i) }
      0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

function Seq#Equal<T>(Seq T, Seq T) returns (bool);
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
  Seq#Equal(s0,s1) <==>
    Seq#Length(s0) == Seq#Length(s1) &&
    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0,j) == Seq#Index(s1,j)));
axiom(forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a,b) }  // extensionality axiom for sequences
  Seq#Equal(a,b) ==> a == b);

function Seq#SameUntil<T>(Seq T, Seq T, int) returns (bool);
axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#SameUntil(s0,s1,n) }
  Seq#SameUntil(s0,s1,n) <==>
    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        0 <= j && j < n ==> Seq#Index(s0,j) == Seq#Index(s1,j)));

function Seq#Take<T>(Seq T, howMany: int) returns (Seq T);
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Take(s,n)) }
  0 <= n ==>
    (n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n) &&
    (Seq#Length(s) < n ==> Seq#Length(Seq#Take(s,n)) == Seq#Length(s)));
axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Take(s,n), j) }
  0 <= j && j < n && j < Seq#Length(s) ==>
    Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));

function Seq#Drop<T>(Seq T, howMany: int) returns (Seq T);
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Drop(s,n)) }
  0 <= n ==>
    (n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n) &&
    (Seq#Length(s) < n ==> Seq#Length(Seq#Drop(s,n)) == 0));
axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Drop(s,n), j) }
  0 <= n && 0 <= j && j < Seq#Length(s)-n ==>
    Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, j+n));

// ---------------------------------------------------------------
// -- Boxing and unboxing ----------------------------------------
// ---------------------------------------------------------------

function $Box<T>(T) returns (ref);
function $Unbox<T>(ref) returns (T);

axiom (forall<T> x: T :: { $Box(x) } $Unbox($Box(x)) == x);

// ---------------------------------------------------------------

type ClassName;
const unique class.int: ClassName;
const unique class.bool: ClassName;
const unique class.object: ClassName;
const unique class.set: ClassName;
const unique class.seq: ClassName;

function dtype(ref) returns (ClassName);
function TypeParams(ref, int) returns (ClassName);

function TypeTuple(a: ClassName, b: ClassName) returns (ClassName);
function TypeTupleCar(ClassName) returns (ClassName);
function TypeTupleCdr(ClassName) returns (ClassName);
// TypeTuple is injective in both arguments:
axiom (forall a: ClassName, b: ClassName :: { TypeTuple(a,b) }
  TypeTupleCar(TypeTuple(a,b)) == a &&
  TypeTupleCdr(TypeTuple(a,b)) == b);

// ---------------------------------------------------------------

type Field alpha;
type HeapType = <alpha>[ref,Field alpha]alpha;

function $IsGoodHeap(HeapType) returns (bool);
var $Heap: HeapType where $IsGoodHeap($Heap);

const unique alloc: Field bool;

function $HeapSucc(HeapType, HeapType) returns (bool);
axiom (forall h: HeapType, k: HeapType :: { $HeapSucc(h,k) }
  $HeapSucc(h,k) ==> (forall o: ref :: { k[o,alloc] } h[o,alloc] ==> k[o,alloc]));
