// RUN: %exits-with 4 %verify --reads-clauses-on-methods "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Regression test: array initializer lambdas were not checked for reads
// clause compliance, unlike seq() constructor lambdas.

class Cell { var data: int }

method Test(c: Cell)
  reads {}
{
  var arr := new int[1](_ reads c => c.data);  // error: insufficient reads
  var mat := new int[2, 2]((_, _) reads c => c.data);  // error: insufficient reads
}
