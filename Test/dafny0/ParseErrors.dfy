// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
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

ghost inductive lemma GhIL()  // error: a lemma is not allowed to be declared "ghost" -- it is already ghost

ghost colemma GhCL()  // error: a lemma is not allowed to be declared "ghost" -- it is already ghost

ghost twostate lemma GhL2()  // error: a lemma is not allowed to be declared "ghost" -- it is already ghost

class C {
  ghost constructor Make()  // error: a constructor is not allowed to be ghost
  ghost method M()
}

// ---------------------- ghost parameters -----------------------------------

method M(ghost x: int) returns (ghost y: int)  // error: ditto

ghost method GM(ghost x: int)  // error: formal not allowed to be declared "ghost" here -- the method is already ghost
  returns (ghost y: int)  // error: ditto

lemma L(ghost x: int)  // error: formal not allowed to be declared "ghost" here -- a lemma is already ghost
  returns (ghost y: int)  // error: ditto

inductive lemma IL(ghost x: int)  // error: formal not allowed to be declared "ghost" here -- a lemma is already ghost
  returns (ghost y: int)  // error: ditto (actually, inductive lemmas are not allowed out-parameters at all)

colemma CoL(ghost x: int)  // error: formal not allowed to be declared "ghost" here -- a lemma is already ghost
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

inductive predicate IP(ghost x: int)  // error: formal not allowed to be declared "ghost" here
                                      // -- an inductive predicate is already ghost
copredicate CoP(ghost x: int)  // error: formal not allowed to be declared "ghost" here
                                      // -- a copredicate is already ghost

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
