// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

// Test case for partial function assignment bug in Rust backend
// This reproduces the issue where assigning a total function (I -> O) 
// to a partial function field (I --> O) fails in Rust compilation

class TestPartialFunction<I, O> {
  const f: I --> O  // Partial function field

  constructor (totalFunc: I -> O)  // Total function parameter
    ensures this.f == totalFunc
  {
    this.f := totalFunc;  // This assignment should work but fails in Rust
  }

  method TestMethod(input: I) returns (output: O)
    requires f.requires(input)
  {
    output := f(input);
  }
}

method Main() {
  // Simple test with int -> int function
  var doubleFunc := (x: int) => x * 2;
  var testObj := new TestPartialFunction(doubleFunc);
  
  var result := testObj.TestMethod(5);
  print "Result: ", result, "\n";
  assert result == 10;
}
