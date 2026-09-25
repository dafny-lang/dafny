// RUN: %exits-with 4 %verify --reads-clauses-on-methods "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Regression test: array initializer lambdas were not checked for reads
// clause compliance, unlike seq() constructor lambdas. The same gap applied to
// the other expressions in an array allocation: the dimension (size)
// expressions, the initializer expression itself, and explicit-display
// elements. All of these now respect the method's reads frame.

class Cell { var data: nat }

// A function whose call reads the heap (the returned lambda does not).
function GetArrow(c: Cell): (int -> int)
  reads c
{ (i: int) => 0 }

method Test(c: Cell)
  reads {}
{
  var arr := new int[1](_ reads c => c.data);  // error: insufficient reads
  var mat := new int[2, 2]((_, _) reads c => c.data);  // error: insufficient reads
}

// The array dimension (size) expression must respect the reads frame.
method TestDimension(c: Cell)
  reads {}
{
  var arr := new int[c.data];  // error: insufficient reads
}

// The initializer expression itself (not just per-index application) must
// respect the reads frame.
method TestInitExpr(c: Cell)
  reads {}
{
  var arr := new int[5](GetArrow(c));  // error: insufficient reads
}

// Explicit-display element expressions must respect the reads frame.
method TestDisplay(c: Cell)
  reads {}
{
  var arr := new int[1] [c.data];  // error: insufficient reads
}

// Legitimate use: reading state that is in the method's reads frame verifies.
method TestOk(c: Cell)
  reads c
{
  var arr := new int[c.data](_ reads c => c.data);
}
