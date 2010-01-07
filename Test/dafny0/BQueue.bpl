// BQueue.bpl
// A queue program specified in the style of dynamic frames.
// Rustan Leino, Michal Moskal, and Wolfram Schulte, 2007.

// ---------------------------------------------------------------

type ref;
const null: ref;

type Field x;

// this variable represents the heap; read its type as \forall \alpha. ref * Field \alpha --> \alpha
type HeapType = <x>[ref, Field x]x;
var H: HeapType;

// every object has an 'alloc' field, which says whether or not the object has been allocated
const unique alloc: Field bool;

// for simplicity, we say that every object has one field representing its abstract value and one
// field representing its footprint (aka frame aka data group).

const unique abstractValue: Field Seq;
const unique footprint: Field [ref]bool;

// ---------------------------------------------------------------

type T;  // the type of the elements of the queue
const NullT: T;  // some value of type T

// ---------------------------------------------------------------

// Queue:
const unique head: Field ref;
const unique tail: Field ref;
const unique mynodes: Field [ref]bool;
// Node:
const unique data: Field T;
const unique next: Field ref;

function ValidQueue(HeapType, ref) returns (bool);
axiom (forall h: HeapType, q: ref ::
  { ValidQueue(h, q) }
  q != null && h[q,alloc] ==>
  (ValidQueue(h, q) <==>
     h[q,head] != null && h[h[q,head],alloc] &&
     h[q,tail] != null && h[h[q,tail],alloc] &&
     h[h[q,tail], next] == null &&
     // The following line can be suppressed now that we have a ValidFootprint invariant
     (forall o: ref :: { h[q,footprint][o] } o != null && h[q,footprint][o] ==> h[o,alloc]) &&
     h[q,footprint][q] &&
     h[q,mynodes][h[q,head]] && h[q,mynodes][h[q,tail]] &&
     (forall n: ref :: { h[q,mynodes][n] }
       h[q,mynodes][n] ==>
           n != null && h[n,alloc] && ValidNode(h, n) &&
           SubSet(h[n,footprint], h[q,footprint]) &&
           !h[n,footprint][q] &&
           (h[n,next] == null ==> n == h[q,tail])
     ) &&
     (forall n: ref :: { h[n,next] }
       h[q,mynodes][n] ==>
           (h[n,next] != null ==> h[q,mynodes][h[n,next]])
     ) &&
     h[q,abstractValue] == h[h[q,head],abstractValue]
  ));

// frame axiom for ValidQueue
axiom (forall h0: HeapType, h1: HeapType, n: ref ::
  { ValidQueue(h0,n), ValidQueue(h1,n) }
  (forall<alpha> o: ref, f: Field alpha :: o != null && h0[o,alloc] && h0[n,footprint][o]
      ==> h0[o,f] == h1[o,f])
  &&
  (forall<alpha> o: ref, f: Field alpha :: o != null && h1[o,alloc] && h1[n,footprint][o]
      ==> h0[o,f] == h1[o,f])
  ==>
  ValidQueue(h0,n) == ValidQueue(h1,n));

function ValidNode(HeapType, ref) returns (bool);
axiom (forall h: HeapType, n: ref ::
  { ValidNode(h, n) }
  n != null && h[n,alloc] ==>
  (ValidNode(h, n) <==>
     // The following line can be suppressed now that we have a ValidFootprint invariant
     (forall o: ref :: { h[n,footprint][o] } o != null && h[n,footprint][o] ==> h[o,alloc]) &&
     h[n,footprint][n] &&
     (h[n,next] != null ==>
         h[h[n,next],alloc] &&
         SubSet(h[h[n,next], footprint], h[n,footprint]) &&
         !h[h[n,next], footprint][n]) &&
     (h[n,next] == null ==> EqualSeq(h[n,abstractValue], EmptySeq)) &&
     (h[n,next] != null ==> EqualSeq(h[n,abstractValue],
                            Append(Singleton(h[h[n,next],data]), h[h[n,next],abstractValue])))
  ));

// frame axiom for ValidNode
axiom (forall h0: HeapType, h1: HeapType, n: ref ::
  { ValidNode(h0,n), ValidNode(h1,n) }
  (forall<alpha> o: ref, f: Field alpha :: o != null && h0[o,alloc] && h0[n,footprint][o]
      ==> h0[o,f] == h1[o,f])
  &&
  (forall<alpha> o: ref, f: Field alpha :: o != null && h1[o,alloc] && h1[n,footprint][o]
      ==> h0[o,f] == h1[o,f])
  ==>
  ValidNode(h0,n) == ValidNode(h1,n));

// ---------------------------------------------------------------

procedure MakeQueue() returns (q: ref)
  requires ValidFootprints(H);
  modifies H;
  ensures ValidFootprints(H);
  ensures ModifiesOnlySet(old(H), H, EmptySet);
  ensures q != null && H[q,alloc];
  ensures AllNewSet(old(H), H[q,footprint]);
  ensures ValidQueue(H, q);
  ensures Length(H[q,abstractValue]) == 0;
{
  var n: ref;

  assume Fresh(H,q);
  H[q,alloc] := true;

  call n := MakeNode(NullT);
  H[q,head] := n;
  H[q,tail] := n;
  H[q,mynodes] := SingletonSet(n);
  H[q,footprint] := UnionSet(SingletonSet(q), H[n,footprint]);
  H[q,abstractValue] := H[n,abstractValue];
}

procedure IsEmpty(q: ref) returns (isEmpty: bool)
  requires ValidFootprints(H);
  requires q != null && H[q,alloc] && ValidQueue(H, q);
  ensures isEmpty <==> Length(H[q,abstractValue]) == 0;
{
  isEmpty := H[q,head] == H[q,tail];
}

procedure Enqueue(q: ref, t: T)
  requires ValidFootprints(H);
  requires q != null && H[q,alloc] && ValidQueue(H, q);
  modifies H;
  ensures ValidFootprints(H);
  ensures ModifiesOnlySet(old(H), H, old(H)[q,footprint]);
  ensures DifferenceIsNew(old(H), old(H)[q,footprint], H[q,footprint]);
  ensures ValidQueue(H, q);
  ensures EqualSeq(H[q,abstractValue], Append(old(H)[q,abstractValue], Singleton(t)));
{
  var n: ref;

  call n := MakeNode(t);

  // foreach m in q.mynodes { m.footprint := m.footprint U n.footprint }
  call BulkUpdateFootprint(H[q,mynodes], H[n,footprint]);
  H[q,footprint] := UnionSet(H[q,footprint], H[n,footprint]);

  // foreach m in q.mynodes { m.abstractValue := Append(m.abstractValue, Singleton(t)) }
  call BulkUpdateAbstractValue(H[q,mynodes], t);
  H[q,abstractValue] := H[H[q,head],abstractValue];

  H[q,mynodes] := UnionSet(H[q,mynodes], SingletonSet(n));

  H[H[q,tail], next] := n;
  H[q,tail] := n;
}

procedure BulkUpdateFootprint(targetSet: [ref]bool, delta: [ref]bool);
  requires ValidFootprints(H);
  modifies H;
  ensures ValidFootprints(H);
  ensures ModifiesOnlySetField(old(H), H, targetSet, footprint);
  ensures (forall o: ref ::
    o != null && old(H)[o,alloc] && targetSet[o]
    ==> H[o,footprint] == UnionSet(old(H)[o,footprint], delta));

procedure BulkUpdateAbstractValue(targetSet: [ref]bool, t: T);
  requires ValidFootprints(H);
  modifies H;
  ensures ValidFootprints(H);
  ensures ModifiesOnlySetField(old(H), H, targetSet, abstractValue);
  ensures (forall o: ref ::
    o != null && old(H)[o,alloc] && targetSet[o]
    ==> EqualSeq(H[o,abstractValue], Append(old(H)[o,abstractValue], Singleton(t))));

procedure Front(q: ref) returns (t: T)
  requires ValidFootprints(H);
  requires q != null && H[q,alloc] && ValidQueue(H, q);
  requires 0 < Length(H[q,abstractValue]);
  ensures t == Index(H[q,abstractValue], 0);
{
  t := H[H[H[q,head], next], data];
}

procedure Dequeue(q: ref)
  requires ValidFootprints(H);
  requires q != null && H[q,alloc] && ValidQueue(H, q);
  requires 0 < Length(H[q,abstractValue]);
  modifies H;
  ensures ValidFootprints(H);
  ensures ModifiesOnlySet(old(H), H, old(H)[q,footprint]);
  ensures DifferenceIsNew(old(H), old(H)[q,footprint], H[q,footprint]);
  ensures ValidQueue(H, q);
  ensures EqualSeq(H[q,abstractValue], Drop(old(H)[q,abstractValue], 1));
{
  var n: ref;

  n := H[H[q,head], next];
  H[q,head] := n;
  // we could also remove old(H)[q,head] from H[q,mynodes], and similar for the footprints
  H[q,abstractValue] := H[n,abstractValue];
}

// --------------------------------------------------------------------------------

procedure MakeNode(t: T) returns (n: ref)
  requires ValidFootprints(H);
  modifies H;
  ensures ValidFootprints(H);
  ensures ModifiesOnlySet(old(H), H, EmptySet);
  ensures n != null && H[n,alloc];
  ensures AllNewSet(old(H), H[n,footprint]);
  ensures ValidNode(H, n);
  ensures H[n,data] == t && H[n,next] == null;
{
  assume Fresh(H,n);
  H[n,alloc] := true;

  H[n,next] := null;
  H[n,data] := t;
  H[n,footprint] := SingletonSet(n);
  H[n,abstractValue] := EmptySeq;
}

// --------------------------------------------------------------------------------

procedure Main(t: T, u: T, v: T)
  requires ValidFootprints(H);
  modifies H;
  ensures ValidFootprints(H);
  ensures ModifiesOnlySet(old(H), H, EmptySet);
{
  var q0, q1: ref;
  var w: T;

  call q0 := MakeQueue();
  call q1 := MakeQueue();

  call Enqueue(q0, t);
  call Enqueue(q0, u);

  call Enqueue(q1, v);

  assert Length(H[q0,abstractValue]) == 2;

  call w := Front(q0);
  assert w == t;
  call Dequeue(q0);

  call w := Front(q0);
  assert w == u;

  assert Length(H[q0,abstractValue]) == 1;
  assert Length(H[q1,abstractValue]) == 1;
}

// --------------------------------------------------------------------------------

procedure Main2(t: T, u: T, v: T, q0: ref, q1: ref)
  requires q0 != null && H[q0,alloc] && ValidQueue(H, q0);
  requires q1 != null && H[q1,alloc] && ValidQueue(H, q1);
  requires DisjointSet(H[q0,footprint], H[q1,footprint]);
  requires Length(H[q0,abstractValue]) == 0;

  requires ValidFootprints(H);
  modifies H;
  ensures ValidFootprints(H);
  ensures ModifiesOnlySet(old(H), H, UnionSet(old(H)[q0,footprint], old(H)[q1,footprint]));
{
  var w: T;

  call Enqueue(q0, t);
  call Enqueue(q0, u);

  call Enqueue(q1, v);

  assert Length(H[q0,abstractValue]) == 2;

  call w := Front(q0);
  assert w == t;
  call Dequeue(q0);

  call w := Front(q0);
  assert w == u;

  assert Length(H[q0,abstractValue]) == 1;
  assert Length(H[q1,abstractValue]) == old(Length(H[q1,abstractValue])) + 1;
}

// ---------------------------------------------------------------

// Helpful predicates used in specs

function ModifiesOnlySet(oldHeap: HeapType, newHeap: HeapType, set: [ref]bool) returns (bool);
axiom (forall oldHeap: HeapType, newHeap: HeapType, set: [ref]bool ::
  { ModifiesOnlySet(oldHeap, newHeap, set) }
  ModifiesOnlySet(oldHeap, newHeap, set) <==>
    NoDeallocs(oldHeap, newHeap) &&
    (forall<alpha> o: ref, f: Field alpha :: { newHeap[o,f] }
      o != null && oldHeap[o,alloc] ==>
      oldHeap[o,f] == newHeap[o,f] || set[o]));

function ModifiesOnlySetField<alpha>(oldHeap: HeapType, newHeap: HeapType,
                                     set: [ref]bool, field: Field alpha) returns (bool);
axiom (forall<alpha> oldHeap: HeapType, newHeap: HeapType, set: [ref]bool, field: Field alpha ::
  { ModifiesOnlySetField(oldHeap, newHeap, set, field) }
  ModifiesOnlySetField(oldHeap, newHeap, set, field) <==>
    NoDeallocs(oldHeap, newHeap) &&
    (forall<beta> o: ref, f: Field beta :: { newHeap[o,f] }
      o != null && oldHeap[o,alloc] ==>
      oldHeap[o,f] == newHeap[o,f] || (set[o] && f == field)));

function NoDeallocs(oldHeap: HeapType, newHeap: HeapType) returns (bool);
axiom (forall oldHeap: HeapType, newHeap: HeapType ::
  { NoDeallocs(oldHeap, newHeap) }
  NoDeallocs(oldHeap, newHeap) <==>
    (forall o: ref :: { newHeap[o,alloc] }
      o != null && oldHeap[o,alloc] ==> newHeap[o,alloc]));

function AllNewSet(oldHeap: HeapType, set: [ref]bool) returns (bool);
axiom (forall oldHeap: HeapType, set: [ref]bool ::
  { AllNewSet(oldHeap, set) }
  AllNewSet(oldHeap, set) <==>
    (forall o: ref :: { oldHeap[o,alloc] }
      o != null && set[o] ==> !oldHeap[o,alloc]));

function DifferenceIsNew(oldHeap: HeapType, oldSet: [ref]bool, newSet: [ref]bool) returns (bool);
axiom (forall oldHeap: HeapType, oldSet: [ref]bool, newSet: [ref]bool ::
  { DifferenceIsNew(oldHeap, oldSet, newSet) }
  DifferenceIsNew(oldHeap, oldSet, newSet) <==>
    (forall o: ref :: { oldHeap[o,alloc] }
      o != null && !oldSet[o] && newSet[o] ==> !oldHeap[o,alloc]));

function ValidFootprints(h: HeapType) returns (bool);
axiom (forall h: HeapType ::
  { ValidFootprints(h) }
  ValidFootprints(h) <==>
    (forall o: ref, r: ref :: { h[o,footprint][r] }
      o != null && h[o,alloc] && r != null && h[o,footprint][r] ==> h[r,alloc]));

function Fresh(h: HeapType, o: ref) returns (bool);
axiom (forall h: HeapType, o: ref ::
  { Fresh(h,o) }
  Fresh(h,o) <==>
    o != null && !h[o,alloc] && h[o,footprint] == SingletonSet(o));

// ---------------------------------------------------------------

const EmptySet: [ref]bool;
axiom (forall o: ref :: { EmptySet[o] } !EmptySet[o]);

function SingletonSet(ref) returns ([ref]bool);
axiom (forall r: ref :: { SingletonSet(r) } SingletonSet(r)[r]);
axiom (forall r: ref, o: ref :: { SingletonSet(r)[o] } SingletonSet(r)[o] <==> r == o);

function UnionSet([ref]bool, [ref]bool) returns ([ref]bool);
axiom (forall a: [ref]bool, b: [ref]bool, o: ref :: { UnionSet(a,b)[o] }
  UnionSet(a,b)[o] <==> a[o] || b[o]);

function SubSet([ref]bool, [ref]bool) returns (bool);
axiom(forall a: [ref]bool, b: [ref]bool :: { SubSet(a,b) }
  SubSet(a,b) <==> (forall o: ref :: {a[o]} {b[o]} a[o] ==> b[o]));

function EqualSet([ref]bool, [ref]bool) returns (bool);
axiom(forall a: [ref]bool, b: [ref]bool :: { EqualSet(a,b) }
  EqualSet(a,b) <==> (forall o: ref :: {a[o]} {b[o]} a[o] <==> b[o]));

function DisjointSet([ref]bool, [ref]bool) returns (bool);
axiom (forall a: [ref]bool, b: [ref]bool :: { DisjointSet(a,b) }
  DisjointSet(a,b) <==> (forall o: ref :: {a[o]} {b[o]} !a[o] || !b[o]));

// ---------------------------------------------------------------

// Sequence of T
type Seq;

function Length(Seq) returns (int);
axiom (forall s: Seq :: { Length(s) } 0 <= Length(s));

const EmptySeq: Seq;
axiom Length(EmptySeq) == 0;
axiom (forall s: Seq :: { Length(s) } Length(s) == 0 ==> s == EmptySeq);

function Singleton(T) returns (Seq);
axiom (forall t: T :: { Length(Singleton(t)) } Length(Singleton(t)) == 1);

function Append(Seq, Seq) returns (Seq);
axiom (forall s0: Seq, s1: Seq :: { Length(Append(s0,s1)) }
  Length(Append(s0,s1)) == Length(s0) + Length(s1));

function Index(Seq, int) returns (T);
axiom (forall t: T :: { Index(Singleton(t), 0) } Index(Singleton(t), 0) == t);
axiom (forall s0: Seq, s1: Seq, n: int :: { Index(Append(s0,s1), n) }
  (n < Length(s0) ==> Index(Append(s0,s1), n) == Index(s0, n)) &&
  (Length(s0) <= n ==> Index(Append(s0,s1), n) == Index(s1, n - Length(s0))));

function EqualSeq(Seq, Seq) returns (bool);
axiom (forall s0: Seq, s1: Seq :: { EqualSeq(s0,s1) }
  EqualSeq(s0,s1) <==>
    Length(s0) == Length(s1) &&
    (forall j: int :: { Index(s0,j) } { Index(s1,j) }
        0 <= j && j < Length(s0) ==> Index(s0,j) == Index(s1,j)));

function Take(s: Seq, howMany: int) returns (Seq);
axiom (forall s: Seq, n: int :: { Length(Take(s,n)) }
  0 <= n ==>
    (n <= Length(s) ==> Length(Take(s,n)) == n) &&
    (Length(s) < n ==> Length(Take(s,n)) == Length(s)));
axiom (forall s: Seq, n: int, j: int :: { Index(Take(s,n), j) }
  0 <= j && j < n && j < Length(s) ==>
    Index(Take(s,n), j) == Index(s, j));

function Drop(s: Seq, howMany: int) returns (Seq);
axiom (forall s: Seq, n: int :: { Length(Drop(s,n)) }
  0 <= n ==>
    (n <= Length(s) ==> Length(Drop(s,n)) == Length(s) - n) &&
    (Length(s) < n ==> Length(Drop(s,n)) == 0));
axiom (forall s: Seq, n: int, j: int :: { Index(Drop(s,n), j) }
  0 <= n && 0 <= j && j < Length(s)-n ==>
    Index(Drop(s,n), j) == Index(s, j+n));

// ---------------------------------------------------------------
