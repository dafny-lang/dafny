// RUN: %exits-with 2 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ---------------------- chaining operators -----------------------------------

method TestChaining0(j: int, k: int, m: int)
  requires j != k != m;  // error: cannot have more than one != per chain
  requires j == k == m;  // dandy
  requires j < k == m == m+1 != m+2 >= 100;  // error: cannot mix < and >=
  requires j >= k == m == m-1 != m-2 < 100;  // error: cannot mix >= and <
{
}

method TestChaining1<T>(s: set<T>, t: set<T>, u: set<T>, x: T, SuperSet: set<set<T>>)
  requires s <= t <= u >= s+u;  // error: cannot mix <= and >=
  ensures s <= u;
  ensures s !! t !! u; // valid, means pairwise disjoint
  ensures x in s in SuperSet;  // error: 'in' is not chaining
  ensures x !in s in SuperSet;  // error: 'in' is not chaining
  ensures x in s !in SuperSet;  // error: 'in' is not chaining
  ensures x in s == t;  // error: 'in' is not chaining
{
}

method TestChaining2(a: set<int>, b: set<int>, c: set<int>)
{
  var x := a !! b !! c;
  var y := a !! b == c;  // error
  var z0 := a == (b !! c);
  var z1 := (a == b) !! c;
  var z2 := a == b !! c;  // error: == and !! do not chain together (regression test)
}

// ---------------------- calc statements -----------------------------------

method TestCalc()
{
  calc {} // OK, empty calculations are allowed
  calc {
	2 + 3; // OK, single-line calculations are allowed
  }
  calc {
	2 + 3;
	calc {  // OK: a calc statement is allowed as a sub-hint
		2;
		1 + 1;
	}
	calc {
		3;
		1 + 2;
	}
	{ assert true; } // OK: multiple subhints are allowed between two lines
	1 + 1 + 1 + 2;
	{ assert 1 + 1 + 1 == 3; }
	{ assert true; }
	3 + 2;
  }
  calc != { // error: != is not allowed as the main operator of a calculation
	2 + 3;
	4;
  }
  calc { // OK, these operators are compatible
	2 + 3;
	> 4;
	>= 2 + 2;
  }
  calc < { // OK, these operators are compatible
	2 + 3;
	== 5;
	<= 3 + 3;
  }
  calc < { // error: cannot mix < and >= or >
	2 + 3;
	>= 5;
	> 2 + 2;
	6;
  }
  calc >= { // error: cannot mix >= and <= or !=
	2 + 3;
	<= 5;
	!= 2 + 2;
	3;
  }
  calc { // error: cannot have more than one != per calc
	2 + 3;
	!= 4;
	!= 1 + 2;
	3;
  }
}

// ---------------------- ghost modifier on methods -----------------------------------

ghost method GhM()

ghost lemma GhL()  // error: a lemma is not allowed to be declared "ghost" -- it is already ghost

ghost least lemma GhIL()  // error: a lemma is not allowed to be declared "ghost" -- it is already ghost

ghost greatest lemma GhCL()  // error: a lemma is not allowed to be declared "ghost" -- it is already ghost

ghost twostate lemma GhL2()  // error: a lemma is not allowed to be declared "ghost" -- it is already ghost

class C {
  constructor Make()
  ghost method M()
}

// ---------------------- ghost parameters -----------------------------------

method M(ghost x: int) returns (ghost y: int)  // error: ditto

ghost method GM(ghost x: int)  // error: formal not allowed to be declared "ghost" here -- the method is already ghost
  returns (ghost y: int)  // error: ditto

lemma L(ghost x: int)  // error: formal not allowed to be declared "ghost" here -- a lemma is already ghost
  returns (ghost y: int)  // error: ditto

least lemma IL(ghost x: int)  // error: formal not allowed to be declared "ghost" here -- a lemma is already ghost
  returns (ghost y: int)  // error: ditto (actually, least lemmas are not allowed out-parameters at all)

greatest lemma CoL(ghost x: int)  // error: formal not allowed to be declared "ghost" here -- a lemma is already ghost
  returns (ghost y: int)  // error: ditto (actually, co-lemmas are not allowed out-parameters at all)

twostate lemma L2(ghost x: int)  // error: formal not allowed to be declared "ghost" here -- a lemma is already ghost
  returns (ghost y: int)  // error: ditto

class C {
  constructor Make(ghost x: int)
  method M(ghost x: int) returns (ghost y: int)
}

function F(ghost x: int): int  // error: formal not allowed to be declared "ghost" here -- a function is already ghost
function method FM(ghost x: int): int
predicate P(ghost x: int)  // error: formal not allowed to be declared "ghost" here -- a predicate is already ghost

least predicate IP(ghost x: int)  // error: formal not allowed to be declared "ghost" here
                                      // -- a least predicate is already ghost
greatest predicate CoP(ghost x: int)  // error: formal not allowed to be declared "ghost" here
                                      // -- a greatest predicate is already ghost

twostate function F2(ghost x: int): int  // error: formal not allowed to be declared "ghost" here -- a function is already ghost
twostate predicate P2(ghost x: int)  // error: formal not allowed to be declared "ghost" here -- a predicate is already ghost

// ------------------------- set and map displays ------------------------------
method Displays()
    // all of these should parse, but at one point they did not
    ensures iset{} == iset{}
    ensures map[] == map[]
    ensures imap[] == imap[]

method SetComprehensionParsingRegression0()
{
  // these once had crashed the parser
  var s0 := set x,y;
  var s1 := set x,y | true;
}

// ------------------------- type members ------------------------------

datatype Dt<A> = Blue | Bucket(diameter: real) | Business(trendy: bool, a: A)
{
  var x: int  // error: mutable fields not allowed in datatypes
}
newtype Pos = x | 0 < x witness 1
{
  var x: int  // error: mutable fields not allowed in newtypes
}
type Opaque {
  var x: int  // error: mutable field not allowed in opaque type
}

// ------------------------- nameonly parameters ------------------------------

module NameOnlyParameters {
  // name-less datatype fields
  datatype D =
    | D0(int, nameonly int) // error: nameonly modifier must be followed by parameter name
    | D1(int, nameonly int, real) // error: nameonly modifier must be followed by parameter name
    | D2(int, nameonly x: int)
  // named function results
  function F(nameonly y: int): int
  function G(y: int): (nameonly r: int) // error: 'nameonly' unexpected here
  // out-parameters
  method M(nameonly x: int) returns (y: int)
  method N(x: int) returns (nameonly y: int) // error: 'nameonly' not allowed here
  // yield-parameters
  iterator Iter0(nameonly x: int) yields (y: int)
  iterator Iter0(x: int) yields (nameonly y: int) // error: 'nameonly' not allowed here
}

// ------------------------- parameters of ghost constructors ------------------------------

module GhostConstructors {
  class Either {
    constructor A(x: int) {
    }
    ghost constructor B(x: int) {
    }
    constructor C(ghost x: int) {
    }
    ghost constructor D(ghost x: int) { // error: don't use 'ghost' keyword for ghost constructor parameters
    }
}
}

// ------------------------- static keyword ------------------------------

module IllegalStatic {
  class C {
    static constructor () // error: constructor cannot be declared 'static'
  }
  static method M() // warning: 'static' not allowed here
  static function F(): int // warning: 'static' not allowed here
  static lemma F() // warning: 'static' not allowed here
  static twostate function F2(): int // warning: 'static' not allowed here
  static least predicate LP() // warning: 'static' not allowed here

  static datatype D = D // error: cannot be 'static'
  static module M { } // error: cannot be 'static'
}

// ------------------------- ghost keyword ------------------------------

module IllegalGhost {
  ghost datatype D = D // error: cannot be 'ghost'
  ghost module M { } // error: cannot be 'ghost'
}

// ------------------------- already-ghost functions ------------------------------

module AlreadyGhost {
  // a twostate function/predicate cannot be used with ...
  ghost twostate function F(): int { 2 } by method { } // error (x2): ... with "by method" or "ghost"
  twostate function method G(): int { 2 } by method { } // error: ... with "by method"
  ghost twostate predicate P() { true } by method { } // error (x2): ... with "by method" or "ghost"
  twostate predicate method Q() { true } by method { } // error: ... with "by method"

  // an extreme predicate cannot be used with ...
  ghost least predicate I() { true } by method { } // error (x2): ... with "by method" or "ghost"
  ghost greatest predicate J() { true } by method { } // error (x2): ... with "by method" or "ghost"

  // a twostate or extreme predicate is not allowed to be declared with either "by method" or "abstract"
  abstract twostate function A0(): int { 2 } by method { } // error (x2)
  abstract twostate predicate A1() { true } by method { } // error (x2)
  abstract least predicate A2() { true } by method { } // error (x2)
  abstract greatest predicate A3() { true } by method { } // error (x2)
}

// ------------------------- 'older' contextual keyword ------------------------------

module Older {
  function F(older x: X): R
  predicate P(older older older x: X)
  least predicate Q(older older older x: X) // error (x3): 'older' is an identifier here
  method M(older x: X) // error: 'older' is an identifier here
  function F(): (older r: R) // error: 'older' is an identifier here

  twostate function W(a: A, new older new older b: B, nameonly older nameonly c: C := "hello"): int
  function method C(a: A, ghost older older b: B, nameonly ghost older nameonly ghost c: C := "hello"): int
  twostate lemma L(nameonly older nameonly c: C := "hello") // error: 'older' is an identifier here
}

// ---------------------- ghost arguments of arrow types -----------------------------------

module ArrowTypes {
  const f: (ghost int, int) -> int // error: arrow-type arguments are not allowed to be ghost

  method M() {
    var g: (real, (ghost int, int), bool) -> int;
    var h: ((ghost int, int)) -> int;
    var i: (bool, ghost real, int, ghost bv6) -> ORDINAL; // error (x2): ghost not allowed
  }
}

// ---------------------- invalid newtype definition -----------------------------------

newtype T {} // error: newtype is expected to have an '='
