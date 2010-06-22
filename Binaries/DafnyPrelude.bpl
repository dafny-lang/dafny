// Dafny prelude
// Created 9 February 2008 by Rustan Leino.
// Converted to Boogie 2 on 28 June 2008.
// Edited sequence axioms 20 October 2009 by Alex Summers.
// Copyright (c) 2008-2010, Microsoft.

// ---------------------------------------------------------------
// -- References -------------------------------------------------
// ---------------------------------------------------------------

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
axiom (forall<T> a: Set T, x: T :: { Set#UnionOne(a, x) }
  Set#UnionOne(a, x)[x]);
axiom (forall<T> a: Set T, x: T, y: T :: { Set#UnionOne(a, x), a[y] }
  a[y] ==> Set#UnionOne(a, x)[y]);

function Set#Union<T>(Set T, Set T) returns (Set T);
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Union(a,b)[o] }
  Set#Union(a,b)[o] <==> a[o] || b[o]);
axiom (forall<T> a, b: Set T, y: T :: { Set#Union(a, b), a[y] }
  a[y] ==> Set#Union(a, b)[y]);
axiom (forall<T> a, b: Set T, y: T :: { Set#Union(a, b), b[y] }
  b[y] ==> Set#Union(a, b)[y]);

function Set#Intersection<T>(Set T, Set T) returns (Set T);
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Intersection(a,b)[o] }
  Set#Intersection(a,b)[o] <==> a[o] && b[o]);

function Set#Difference<T>(Set T, Set T) returns (Set T);
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Difference(a,b)[o] }
  Set#Difference(a,b)[o] <==> a[o] && !b[o]);
axiom (forall<T> a, b: Set T, y: T :: { Set#Difference(a, b), b[y] }
  b[y] ==> !Set#Difference(a, b)[y] );

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
  0 <= len ==> Seq#Length(Seq#Build(s,i,v,len)) == len);

function Seq#Append<T>(Seq T, Seq T) returns (Seq T);
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Length(Seq#Append(s0,s1)) }
  Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));

function Seq#Index<T>(Seq T, int) returns (T);
axiom (forall<T> t: T :: { Seq#Index(Seq#Singleton(t), 0) } Seq#Index(Seq#Singleton(t), 0) == t);
axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) }
  (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)) &&
  (Seq#Length(s0) <= n ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, n - Seq#Length(s0))));
axiom (forall<T> s: Seq T, i: int, v: T, len: int, n: int :: { Seq#Index(Seq#Build(s,i,v,len),n) }
  0 <= n && n < len ==>
    (i == n ==> Seq#Index(Seq#Build(s,i,v,len),n) == v) &&
    (i != n ==> Seq#Index(Seq#Build(s,i,v,len),n) == Seq#Index(s,n)));

function Seq#Update<T>(Seq T, int, T) returns (Seq T);
axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Length(Seq#Update(s,i,v)) }
  0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s,i,v)) == Seq#Length(s));
axiom (forall<T> s: Seq T, i: int, v: T, n: int :: { Seq#Index(Seq#Update(s,i,v),n) }
  0 <= n && n < Seq#Length(s) ==>
    (i == n ==> Seq#Index(Seq#Update(s,i,v),n) == v) &&
    (i != n ==> Seq#Index(Seq#Update(s,i,v),n) == Seq#Index(s,n)));

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
    (0 <= i && i < len && x == v)  ||  
    (exists j: int :: { Seq#Index(s,j) } 0 <= j && j < Seq#Length(s) && j < len && j!=i && Seq#Index(s,j) == x));
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

function Seq#Take<T>(s: Seq T, howMany: int) returns (Seq T);
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Take(s,n)) }
  0 <= n ==>
    (n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n) &&
    (Seq#Length(s) < n ==> Seq#Length(Seq#Take(s,n)) == Seq#Length(s)));
axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Take(s,n), j) } {:weight 25}
  0 <= j && j < n && j < Seq#Length(s) ==>
    Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));

function Seq#Drop<T>(s: Seq T, howMany: int) returns (Seq T);
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

// ---------------------------------------------------------------
// -- If then else -----------------------------------------------
// ---------------------------------------------------------------

function $ite<T>(bool, T, T): T;
axiom (forall<T> g: bool, a,b: T :: { $ite(g,a,b) }
  (g ==> $ite(g,a,b) == a) && (!g ==> $ite(g,a,b) == b));

// ---------------------------------------------------------------
// -- Boxing and unboxing ----------------------------------------
// ---------------------------------------------------------------

type BoxType;

function $Box<T>(T) returns (BoxType);
function $Unbox<T>(BoxType) returns (T);

axiom (forall<T> x: T :: { $Box(x) } $Unbox($Box(x)) == x);
axiom (forall b: BoxType :: { $Unbox(b): int } $Box($Unbox(b): int) == b);
axiom (forall b: BoxType :: { $Unbox(b): ref } $Box($Unbox(b): ref) == b);
axiom (forall b: BoxType :: { $Unbox(b): Set BoxType } $Box($Unbox(b): Set BoxType) == b);
axiom (forall b: BoxType :: { $Unbox(b): Seq BoxType } $Box($Unbox(b): Seq BoxType) == b);
axiom (forall b: BoxType :: { $Unbox(b): DatatypeType } $Box($Unbox(b): DatatypeType) == b);
// note: an axiom like this for bool would not be sound

// ---------------------------------------------------------------
// -- Encoding of type names -------------------------------------
// ---------------------------------------------------------------

type ClassName;
const unique class.int: ClassName;
const unique class.bool: ClassName;
const unique class.object: ClassName;
const unique class.set: ClassName;
const unique class.seq: ClassName;
const unique class.array: ClassName;

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
// -- Datatypes --------------------------------------------------
// ---------------------------------------------------------------

type DatatypeType;

type DtCtorId;
function DatatypeCtorId(DatatypeType) returns (DtCtorId);

function DtRank(DatatypeType) returns (int);

// ---------------------------------------------------------------
// -- Axiom contexts ---------------------------------------------
// ---------------------------------------------------------------

// used to make sure function axioms are not used while their consistency is being checked
const $ModuleContextHeight: int;
const $FunctionContextHeight: int;
const $InMethodContext: bool;

// ---------------------------------------------------------------
// -- Fields -----------------------------------------------------
// ---------------------------------------------------------------

type Field alpha;

type FieldCategory;
const unique $NamedField: FieldCategory;
const unique $IndexedField: FieldCategory;
function FCat<T>(Field T): FieldCategory;

const unique alloc: Field bool;
axiom FCat(alloc) == $NamedField;

function IndexField(int): Field BoxType;
axiom (forall i: int :: { IndexField(i) } FCat(IndexField(i)) == $IndexedField);
function IndexField_Inverse<T>(Field T): int;
axiom (forall i: int :: { IndexField(i) } IndexField_Inverse(IndexField(i)) == i);

function DeclType<T>(Field T) returns (ClassName);

// ---------------------------------------------------------------
// -- Arrays -----------------------------------------------------
// ---------------------------------------------------------------

function Array#Length(ref): int;
axiom (forall r: ref :: 0 <= Array#Length(r));

procedure UpdateArrayRange(arr: ref, low: int, high: int, rhs: BoxType);
  modifies $Heap;
  ensures $HeapSucc(old($Heap), $Heap);
  ensures (forall i: int :: { $Heap[arr, IndexField(i)] } low <= i && i < high ==> $Heap[arr, IndexField(i)] == rhs);
  ensures (forall<alpha> o: ref, f: Field alpha :: { $Heap[o,f] } $Heap[o,f] == old($Heap)[o,f] ||
            (o == arr && FCat(f) == $IndexedField && low <= IndexField_Inverse(f) && IndexField_Inverse(f) < high));

// ---------------------------------------------------------------
// -- The heap ---------------------------------------------------
// ---------------------------------------------------------------

type HeapType = <alpha>[ref,Field alpha]alpha;

function $IsGoodHeap(HeapType) returns (bool);
var $Heap: HeapType where $IsGoodHeap($Heap) && #cev_var_update(#cev_pc, cev_implicit, #loc.$Heap, $Heap);
const unique #loc.$Heap: $token;

function $HeapSucc(HeapType, HeapType) returns (bool);
axiom (forall<alpha> h: HeapType, r: ref, f: Field alpha, x: alpha :: { h[r,f:=x] }
  $HeapSucc(h, h[r,f:=x]));
axiom (forall a,b,c: HeapType :: { $HeapSucc(a,b), $HeapSucc(b,c) }
  $HeapSucc(a,b) && $HeapSucc(b,c) ==> $HeapSucc(a,c));
axiom (forall h: HeapType, k: HeapType :: { $HeapSucc(h,k) }
  $HeapSucc(h,k) ==> (forall o: ref :: { k[o,alloc] } h[o,alloc] ==> k[o,alloc]));

// ---------------------------------------------------------------
// -- Arithmetic -------------------------------------------------
// ---------------------------------------------------------------

// the connection between % and /
axiom (forall x:int, y:int :: {x % y} {x / y}  x % y == x - x / y * y);

// sign of denominator determines sign of remainder
axiom (forall x:int, y:int :: {x % y}  0 < y  ==>  0 <= x % y  &&  x % y < y);
axiom (forall x:int, y:int :: {x % y}  y < 0  ==>  y < x % y  &&  x % y <= 0);

// the following axiom has some unfortunate matching, but it does state a property about % that
// is sometime useful
axiom (forall a: int, b: int, d: int :: { a % d, b % d } 2 <= d && a % d == b % d && a < b  ==>  a + d <= b);

// ---------------------------------------------------------------
// -- CEV (counterexample visualizer) ----------------------------
// ---------------------------------------------------------------

type $token;
function $file_name_is(id:int, tok:$token) returns(bool);


type cf_event;
type var_locglob;

const unique conditional_moment : cf_event;
const unique took_then_branch : cf_event;
const unique took_else_branch : cf_event;

const unique loop_register : cf_event;
const unique loop_entered : cf_event;
const unique loop_exited : cf_event;

const unique cev_local : var_locglob;
const unique cev_global : var_locglob;
const unique cev_parameter : var_locglob;
const unique cev_implicit : var_locglob;


function #cev_init(n:int) returns(bool);

function #cev_save_position(n:int) returns($token);

function #cev_var_intro<T,U>(n:int, locorglob:var_locglob, name:$token, val:T, typ: U) returns(bool);

function #cev_var_update<T>(n:int, locorglob:var_locglob, name:$token, val:T) returns(bool);

function #cev_control_flow_event(n:int, tag : cf_event) returns(bool);

function #cev_function_call(n:int) returns(bool);



var #cev_pc: int;

procedure CevVarIntro<T>(pos: $token, locorglob: var_locglob, name: $token, val: T);
  modifies #cev_pc;
  ensures #cev_var_intro(old(#cev_pc), locorglob, name, val, 0);
  ensures #cev_save_position(old(#cev_pc)) == pos;
  ensures #cev_pc == old(#cev_pc) + 1;

procedure CevUpdateHere<T>(name: $token, val: T);
  ensures #cev_var_update(#cev_pc, cev_local, name, val);

procedure CevStep(pos: $token);
  modifies #cev_pc;
  ensures #cev_save_position(old(#cev_pc)) == pos;
  ensures #cev_pc == old(#cev_pc) + 1;

// CevUpdate == CevUpdateHere + CevStep
procedure CevUpdate<T>(pos: $token, name: $token, val: T);
  modifies #cev_pc;
  ensures #cev_var_update(old(#cev_pc), cev_local, name, val);
  ensures #cev_save_position(old(#cev_pc)) == pos;
  ensures #cev_pc == old(#cev_pc) + 1;

procedure CevUpdateHeap(pos: $token, name: $token, val: HeapType);
  modifies #cev_pc;
  ensures #cev_var_update(old(#cev_pc), cev_implicit, name, val);
  ensures #cev_save_position(old(#cev_pc)) == pos;
  ensures #cev_pc == old(#cev_pc) + 1;

procedure CevEvent(pos: $token, tag: cf_event);
  modifies #cev_pc;
  ensures #cev_control_flow_event(old(#cev_pc), tag);
  ensures #cev_save_position(old(#cev_pc)) == pos;
  ensures #cev_pc == old(#cev_pc) + 1;

procedure CevStepEvent(pos: $token, tag: cf_event);
  modifies #cev_pc;
  ensures #cev_control_flow_event(old(#cev_pc)+1, tag);
  ensures #cev_save_position(old(#cev_pc)+1) == pos;
  ensures #cev_pc == old(#cev_pc) + 2;

procedure CevPreLoop(pos: $token) returns (oldPC: int);
  modifies #cev_pc;
  ensures #cev_control_flow_event(old(#cev_pc), conditional_moment);
  ensures #cev_save_position(old(#cev_pc)) == pos;
  ensures oldPC == old(#cev_pc) && #cev_pc == old(#cev_pc) + 1;

// ---------------------------------------------------------------
