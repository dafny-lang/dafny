// RUN: %exits-with 4 %verify --reads-clauses-on-methods --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var x: int
  var y: int
}

function ReadField(s: seq<C>, c': C): bool
  requires |s| > 4
  reads s[2]
  reads {s[3]}`x
  reads {s[4]}`y
{
  s[0].x == 1 || s[1].y == 1
}

function ReadArrayElement(s: seq<array<int>>): bool
  requires |s| > 2
  reads s[1]
  reads set a | a in s[2..]
{
  if s[0].Length > 0 then s[0][0] == 1 else false
}

function ReadRangeOfArrayElements(s: seq<array<int>>): bool
  requires |s| > 2
  reads s[1]
  reads set a | a in s[2..]
{
  if s[0].Length > 0 then s[0][0..1] == [2, 3] else false
}

function ReadMultiDimArrayElement(s: seq<array2<int>>): bool
  requires |s| > 2
  reads s[1]
  reads set a | a in s[2..]
{
  if s[0].Length0 > 0 && s[0].Length1 > 1 then s[0][0, 1] == 2 else false
}

function ReadByApply(s: seq<C>): bool
  requires |s| > 5
  reads s[3]
  reads {s[4]}`x
  reads {s[5]}`y
{
  var lam := (s': seq<C>)
    requires |s'| > 2
    reads if |s'| > 0 then {s'[0]} else {}
    reads (if |s'| > 1 then {s'[1]} else {})`x
    reads (if |s'| > 2 then {s'[2]} else {})`y
    => false;
  lam(s)
}

function ReadingFunction(s': seq<C>): bool
  requires |s'| > 2
  reads s'[0]
  reads {s'[1]}`x
  reads {s'[2]}`y
{
  false
}

function ReadByFunctionCall(s: seq<C>): bool
  requires |s| > 5
  reads s[3]
  reads {s[4]}`x
  reads {s[5]}`y
{
  ReadingFunction(s)
}

function ReadByReadsCall(s: seq<C>): bool
  requires |s| > 5
  reads s[3]
  reads {s[4]}`x
  reads {s[5]}`y
{
  ghost var r := ReadingFunction.reads(s);
  false
}

method ReadByUnchanged(s: seq<C>)
  requires |s| > 5
  reads s[3]
  reads {s[4]}`x
  reads {s[5]}`y
{
  assert unchanged(s[0], {s[1]}`x, {s[2]}`y);
}

method ReadBySeqInit(s: seq<C>)
  requires |s| > 5
  reads s[3]
  reads {s[4]}`x
  reads {s[5]}`y
{
  var init := i
    reads s[0]
    reads {s[1]}`x
    reads {s[2]}`y
    => false;
  var s' := seq(1, init);
}

method ReadingMethod(s': seq<C>)
  requires |s'| > 2
  reads s'[0]
  reads {s'[1]}`x
  reads {s'[2]}`y
{ }

method ReadByCall(s: seq<C>)
  requires |s| > 5
  reads s[3]
  reads {s[4]}`x
  reads {s[5]}`y
{
  ReadingMethod(s);
}

// tests successful handling of FunctionCallExpr where the receiver isn't a method or function
function Sum(f: int ~> real, lo: int, hi: int): real
  requires lo <= hi
  requires forall i :: lo <= i < hi ==> f.requires(i)
  reads set i, o | lo <= i < hi && o in f.reads(i) :: o
  decreases hi - lo
{
  if lo == hi then 0.0 else
    f(lo) + Sum(f, lo + 1, hi)
}