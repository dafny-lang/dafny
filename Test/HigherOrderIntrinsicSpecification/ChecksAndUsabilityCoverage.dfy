// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Tests for well-formedness of FunctionCallExpr

function MyFunction(x: int, S: set<object>): real
  requires x < 100
  reads S
{
  assert true;
  (x + 12) as real
}

// In methods, there are no reads checks:

method MCaller0(x: int, S: set<object>) {
  var myFunctionRequires := MyFunction.requires(x, S);
  var myFunctionReads := MyFunction.reads(x, S); // error: precondition (x < 100) may not hold
}

method MCaller1(S: set<object>) {
  var myFunctionRequires := MyFunction.requires(5, S);
  var myFunctionReads := MyFunction.reads(5, S);
}

// In functions, reads checks also matter:

// .requires

function FCallerRequires0(x: int, S: set<object>): real
{
  var myFunctionRequires := MyFunction.requires(x, S); // error: insufficient reads clause to call MyFunction.requires, since it may return false
  3.14
}

function FCallerRequires1(S: set<object>): real {
  var myFunctionRequires := MyFunction.requires(5, S); // error: insufficient reads clause to call MyFunction.requires
  3.14
}

function FCallerRequires2(S: set<object>): real
  reads S
{
  var myFunctionRequires := MyFunction.requires(5, S);
  assert myFunctionRequires;
  3.14
}

function FCallerRequires3(S: set<object>): real
  requires MyFunction.requires(5, S) // error: insufficient reads clause
{
  var myFunctionRequires := MyFunction.requires(5, S);
  assert myFunctionRequires;
  3.14
}

function FCallerRequires4(S: set<object>): real
  requires MyFunction.requires(5, S)
  reads S
{
  var myFunctionRequires := MyFunction.requires(5, S);
  assert myFunctionRequires;
  3.14
}

// .reads

function FCallerReads0(x: int, S: set<object>): real {
  var myFunctionReads := MyFunction.reads(x, S); // error (x2): precondition failure and insufficient reads clause
  3.14
}

function FCallerReads1(S: set<object>): real {
  var myFunctionReads := MyFunction.reads(5, S); // error: insufficient reads clause
  3.14
}

function FCallerReads2(x: int, S: set<object>): real
  reads S
{
  var myFunctionReads := MyFunction.reads(x, S); // error: precondition failure (but under the assumption that precondition holds, reads clause is good)
  3.14
}

function FCallerReads3(S: set<object>): real
  reads S
{
  var myFunctionReads := MyFunction.reads(5, S);
  3.14
}

function FCallerReads4(S: set<object>): real
  requires MyFunction.requires(5, S)
  reads MyFunction.reads(5, S)
{
  var myFunctionRequires := MyFunction.requires(5, S);
  var myFunctionReads := MyFunction.reads(5, S);
  assert myFunctionRequires;
  assert myFunctionReads == S;
  3.14
}

// Usability tests

ghost function CallIfPossible0(x: int, S: set<object>): real {
  if MyFunction.requires(x, S) then // error: insufficient reads clause to call MyFunction.requires
    MyFunction(x, S)
  else
    2.7
}

ghost function CallIfPossible1(x: int, S: set<object>): real
  reads MyFunction.reads(x, S) // error: precondition may not hold
{
  if MyFunction.requires(x, S) then // under the assumption that the specification of CallIfPossible1 is well-formed, this line is fine
    MyFunction(x, S)
  else
    2.7
}

ghost function CallIfPossible2(x: int, S: set<object>): real
  reads S
{
  if MyFunction.requires(x, S) then // error: if MyFunction.requires(x, S) returns false, then this could read anything (TODO)
    MyFunction(x, S)
  else
    assert false; // error: control can indeed reach this point
    2.7
}

ghost function CallIfPossible3(x: int, S: set<object>): real
  requires x < 100
{
  if MyFunction.requires(x, S) then // error: insufficient reads clause
    MyFunction(x, S)
  else
    2.7
}

ghost function CallIfPossible4(x: int, S: set<object>): real
  requires x < 100
  reads S
{
  if MyFunction.requires(x, S) then // fine
    MyFunction(x, S)
  else
    assert false; // fine, since control never reaches this point
    2.7
}

// Tests for axioms that can be used to reason about ApplyExpr

method MApply0(x: int, S: set<object>) {
  var req := MyFunction.requires;
  assert req(5, S);
  assert req(x, S); // error: this assertion may not hold
}

method MApply1(x: int, S: set<object>) {
  var rds := MyFunction.reads;
  assert rds(5, S) == S;
  var s := rds(x, S); // error: precondition may not hold
}

method MApply2(x: int, S: set<object>) {
  var req := MyFunction.requires;
  var rds := MyFunction.reads;
  assert req(x, S) ==> rds(x, S) == S;
}

method MApply3(x: int, S: set<object>) {
  var req := MyFunction.requires;
  assert req(x, S) <==> x < 100;
  var rds := MyFunction.reads;
  assert req(x, S) ==> rds(x, S) == S;
}

// Usability tests

method Usability0(x: int, f: int ~> real, g: int --> real, h: int -> real) returns (ghost r: real) {
  if f.requires(x) {
    r := f(x);
  }
  if g.requires(x) {
    r := g(x);
  }
  if
  case true =>
    r := f(x); // error: precondition may not hold
  case true =>
    r := g(x); // error: precondition may not hold
  case true =>
    r := h(x);
}

ghost function Usability1(x: int, f: int ~> real, g: int --> real, h: int -> real): real {
  var r0 := if f.requires(x) then f(x) else 30.0; // error: insufficient reads clause to call f.requires(x)
  var r1 := if g.requires(x) then g(x) else 30.0;
  var r2 := f(x); // error: precondition may not hold
  var r3 := g(x); // error: precondition may not hold
  var r4 := h(x);
  r0 + r1 + r2 + r3 + r4
}

ghost function Usability2(x: int, f: int ~> real, g: int --> real, h: int -> real): real
  reads f.requires.reads(x)
{
  var r0 := if f.requires(x) then f(x) else 30.0; // fine
  var r1 := if g.requires(x) then g(x) else 30.0;
  var r2 := f(x); // error: precondition may not hold
  var r3 := g(x); // error: precondition may not hold
  var r4 := h(x);
  r0 + r1 + r2 + r3 + r4
}

ghost function Usability3(x: int, f: int ~> real, g: int --> real, h: int -> real): real
  reads f.reads(x) // error: precondition of f.reads(x) may not hold
{
  var r0 := if f.requires(x) then f(x) else 30.0;
  var r1 := if g.requires(x) then g(x) else 30.0;
  var r2 := f(x); // under the assumption that the specification of Usability3 is well-formed, this line is fine
  var r3 := g(x); // error: precondition may not hold
  var r4 := h(x);
  r0 + r1 + r2 + r3 + r4
}

ghost function Usability4(x: int, f: int ~> real, g: int --> real, h: int -> real): real
  requires f.requires(x)
  reads f.reads(x)
{
  var r0 := if f.requires(x) then f(x) else 30.0;
  var r1 := if g.requires(x) then g(x) else 30.0;
  var r2 := f(x);
  var r3 := g(x); // error: precondition may not hold
  var r4 := h(x);
  r0 + r1 + r2 + r3 + r4
}

method Usability5(x: int, g: int --> real, h: int -> real) {
  assert g.requires(x) ==> g.reads(x) == {};
  assert g.reads(x) == {}; // error: this is known to hold only if g.requires(x) holds (TODO: is this a surprise or awkward?)

  assert h.requires(x);
  assert h.reads(x) == {};
}

method Usability6(x: int, f: int ~> real) {
  // The following is called Axiom 1 in the PR description:
  assert f.requires(x) ==> f.reads.requires(x);
  assert f.reads.requires(x) ==> f.requires(x); // TODO

  // The following is called Axiom 2 in the PR description:
  assert f.requires(x) ==> f.reads.reads(x) == f.reads(x);

  // The following is called Axiom 3 in the PR description:
  assert f.requires.requires(x);

  // The following is called Axiom 4 in the PR description:
  assert f.requires(x) ==> f.requires.reads(x) == f.reads(x);
}

method Usability7(x: int, g: int --> real) {
  assert g.requires(x) ==> g.reads(x) == {};

  assert g.requires(x) ==> g.reads.requires(x);
  assert g.reads.requires(x) ==> g.requires(x); // TODO

  assert g.requires(x) ==> g.reads.reads(x) == {};

  assert g.requires.requires(x);
  assert g.requires(x) ==> g.requires.reads(x) == {};
}

method Usability8(x: int, h: int -> real) {
  assert h.requires(x);
  assert h.reads(x) == {};

  assert h.reads.requires(x);
  assert h.reads.reads(x) == {};

  assert h.requires.requires(x);
  assert h.requires.reads(x) == {};
}

// Framing

class Cell {
  var data: int
}

method Framing0(x: int, f: int ~> real, cell: Cell)
  requires f.requires(x) && f(x) == 8.0
  requires cell !in f.reads(x)
  modifies cell
{
  cell.data := cell.data + 1;
  assert f.requires(x) && f(x) == 8.0;
}

method Framing1(x: int, f: int ~> real)
  requires f.requires(x) && f(x) == 8.0
{
  var cell := new Cell;
  cell.data := cell.data + 1;
  assert f.requires(x) && f(x) == 8.0;
}

method Framing2(x: int, f: int ~> real, cell: Cell)
  requires f.requires(x) && f(x) == 8.0
  modifies cell
{
  cell.data := cell.data + 1;
  assert f.requires(x); // error: assertion may not hold
  assert f(x) == 8.0; // error: assertion may not hold
}