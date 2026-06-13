// RUN: %build -t:lib "%s" --output "%S/Output/git-issue-6436.doo" > "%t"
// RUN: %verify "%S/Output/git-issue-6436.doo" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Regression test: a set comprehension (a `set i | ...` with a single bound variable and an
// implicit term) appearing as a NON-LAST element of a comma-separated list lost its parentheses
// when serialized to a .doo file. On reload the parser greedily absorbs the following `, <ident>`
// as a second bound variable of the comprehension, producing a parse error. The fix parenthesizes
// such non-last elements in every comma-list printer. The trailing element must be an identifier to
// trigger the original parser ambiguity, so each case below uses one.

predicate g(x: set<nat>, y: nat)

// Function-call argument and first-class function application (ApplyExpr).
predicate f(x: set<nat>, y: nat) { g((set i <- x), y) }
ghost predicate h(p: (set<nat>, nat) -> bool, x: set<nat>, y: nat) { p((set i <- x), y) }

datatype R = R(a: set<nat>, b: nat)

// Datatype value and datatype update.
function DVal(x: set<nat>, z: nat): R { R((set i <- x), z) }
function DtUpdate(r: R, x: set<nat>, n: nat): R { r.(a := (set i <- x), b := n) }

// Set / sequence / multiset displays.
function SetD(x: set<nat>, z: set<nat>): set<set<nat>> { {(set i <- x), z} }
function SeqD(x: set<nat>, z: set<nat>): seq<set<nat>> { [(set i <- x), z] }
function MSetD(x: set<nat>, z: set<nat>): multiset<set<nat>> { multiset{(set i <- x), z} }

// Map display, in the value position.
function MapV(x: set<nat>, k0: nat, k1: nat): map<nat, set<nat>> { map[k0 := (set i <- x), k1 := {}] }

// Let with multiple right-hand sides.
function LetRhs(x: set<nat>, z: nat): nat { var a, b := (set i <- x), z; b }

// decreases clause.
function Dec(x: set<nat>, n: nat): nat
  decreases (set i <- x), n
{ if n == 0 then 0 else Dec(x, n - 1) }

class C { var f: int }

// reads clause.
function Reads(s: set<C>, o: C): int reads (set c <- s), o { 0 }

// modifies clause and modify statement.
method Modifies(s: set<C>, o: C) modifies (set c <- s), o { }
method ModifyStmt(s: set<C>, o: C) modifies s, o { modify (set c <- s), o; }

// Attribute arguments and print statement.
method {:myattr (set i <- {1, 2}), 7} Attr() { }
method PrintStmt(x: set<nat>, n: nat) { print (set i <- x), n; }

// return and := right-hand-side lists.
method Return(x: set<nat>, z: nat) returns (a: set<nat>, b: nat) { return (set i <- x), z; }
method Assign(x: set<nat>, z: nat) returns (a: set<nat>, b: nat) { a, b := (set i <- x), z; }
