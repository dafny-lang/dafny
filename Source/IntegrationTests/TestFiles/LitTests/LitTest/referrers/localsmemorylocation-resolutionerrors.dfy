// RUN: %exits-with 2 %resolve --referrers --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Test {
  var x: int
  constructor() {
    x := 0;
  }
}

method LocalVars(x: Test)
  ensures locals`i == locals`i // WF Error: Local variable names cannot appear in contracts
{
  var i := new Test();
  var mem_j := locals`j; // j not declared (yet)
  var k := LocalVars`x; // To designate the input parameter memory location, use locals`x
  var j := new Test();
}


method Parameters(i: Test, ghost mem_i: (object, field)) returns (r: Test, ghost mem_r: (object, field))
  requires mem_i == locals`r // Error: r is not declared in ensures scope
{
  var mem_i2 := locals`i;
  var mem_j := locals`j; // j not declared (yet)
  var mem_k := locals`k; // k not declared (not at all)
  var j := new Test();
}

method CallParameters() {
  var test := new Test();
  Parameters(test, locals`i); // locals`i is not defined. Did you mean in this context 'Parameters`i?'
  Parameters(test, Parameters`k); // Parameters`k is not defined. Available in context: Parameters`i, locals`test, Parameters`mem_i
}

function FunctionParametersAreNoLocalsMemoryLocation(i: Test): int {
  var mem_i := locals`i; // Function don't have local memory locations, all their variables are only intermediates.
  1
}

method SingleParam(ghost mem_i: (object, field)) {
}

method CallSingleParam() {
  SingleParam(SingleParam`mem_j); // Did you mean SingleParam`mem_i?
  SingleParam(CallSingleParam`mem_i); // Did you mean SingleParam`mem_i?
  SingleParam(NonExistingMethod`mem_i); // Did you mean NonExistingMethod`mem_i?
}

function NoLocals(i: Test): (object, field) {
  locals`i // Error: field location expressions cannot be used outside of a method
}