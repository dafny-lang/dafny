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
    ensures output == f(input)
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
  
  // The assertion should hold because doubleFunc(5) = 5 * 2 = 10
  assert doubleFunc.requires(5);  // Total functions are defined everywhere
  assert doubleFunc(5) == 10;     // 5 * 2 = 10
  assert testObj.f == doubleFunc;  // From constructor postcondition
  assert result == 10;             // Therefore result should be 10
}
