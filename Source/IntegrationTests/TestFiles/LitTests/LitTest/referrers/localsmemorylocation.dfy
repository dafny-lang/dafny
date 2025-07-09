// RUN: %verify --referrers --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class TestLocals {
  var x: int
  constructor() {
    x := 0;
  }
}

method LocalVars() {
  var i := new TestLocals();
  var j := new TestLocals();
  
  var mem_i := locals`i;
  assert mem_i == locals`i;
  assert mem_i != locals`j;
  assert locals`j != j`x;
}

method Parameters(i: TestLocals, ghost mem_i: (object, field)) returns (r: TestLocals, ghost mem_r: (object, field))
  decreases *
  requires mem_i == locals`i // We want to be able to express memory locations on parameters in contracts
  ensures mem_r == locals`r  // Same here
{
  var mem_i2 := locals`i;
  var mem_r2 := locals`r;
  mem_r := locals`r;
  r := i;
  var _, _ := Parameters(i, Parameters`i) by {
    assert Parameters`i != locals`i; // Recursive calls should have different memory locations
  }
}

method CallParameters()
  decreases * {
  var test := new TestLocals();
  var i := new TestLocals();
  var test2, memTest2 := Parameters(i := test, mem_i := Parameters`i) by {
    assert Parameters`i != locals`i; // All fields are unique
  }
  assert memTest2 != locals`test2; // From the ensures of parameters.
}

method CallParametersNoLocalI()
  decreases * {
  var test := new TestLocals();
  var test2, memTest2 := Parameters(i := test, mem_i := Parameters`i);
}

method SingleParam(ghost mem_i: (object, field)) {
}

method CallSingleParam() {
  SingleParam(SingleParam`mem_i);
}

method OnlyStackMemoryLocations(t: TestLocals, s: set<(object, field)>)
  requires forall r <- s :: r.0 == locals
  decreases *
{
  var alias_t := t;
  OnlyStackMemoryLocations(t, s + {locals`alias_t, OnlyStackMemoryLocations`t});
}