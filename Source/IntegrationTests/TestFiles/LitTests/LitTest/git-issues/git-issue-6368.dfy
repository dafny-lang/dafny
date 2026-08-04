// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Regression test: SeqConstructionExpr and SeqUpdateExpr were missing
// CheckResultToBeInType, so newtype constraints were not checked.

newtype pos = i: seq<nat> | |i| > 0 witness [0]

function Bar(n: nat): pos { seq(n, i => i) }  // error: constraint not satisfied

function Baz(n: nat): pos
  requires n > 0
{ seq(n, i => i) }  // ok

// Also test collection update expressions on newtypes:
newtype smallmap = m: map<int,int> | |m| <= 1 witness map[]

function MapUpdate(m: smallmap, k: int, v: int): smallmap { m[k := v] }  // error

newtype smallmset = m: multiset<int> | m[0] <= 1 witness multiset{}

function MsetUpdate(m: smallmset): smallmset { m[0 := 5] }  // error

newtype sortedseq = s: seq<int> | forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j] witness []

function SeqUpdate(s: sortedseq): sortedseq
  requires |s| >= 2
{ s[0 := 999] }  // error: might break sorted order

// The same omission affected the two bool-producing constructions whose result is constrained only to the
// bool *family*, so that a newtype based on bool is an accepted result type: `decreases to` and `unchanged`.
// With the constraint unchecked, the function's postcondition axiom supplied a contradiction to its callers.

newtype TrueBool = b: bool | b witness true

ghost function DecreasesTo(): TrueBool { 1 decreases to 2 }  // error: the value is false

ghost function DecreasesToOk(): TrueBool { 2 decreases to 1 }  // ok

class Cell { var data: int }

twostate function Unchanged(c: Cell): TrueBool reads c { unchanged(c) }  // error: c may have changed

twostate function UnchangedOk(c: Cell): TrueBool reads c
  requires unchanged(c)
{ unchanged(c) }  // ok

// A plain bool result is unaffected, since there is no constraint to check.
twostate predicate PlainUnchanged(c: Cell) reads c { unchanged(c) }
ghost function PlainDecreasesTo(): bool { 1 decreases to 2 }
