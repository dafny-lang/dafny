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
