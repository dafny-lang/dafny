// RUN: %testDafnyForEachCompiler "%s" -- --standard-libraries

// This is just a basic test of the mechanism to make the standard libraries
// available to user code in general.
// The DafnyStandardLibraries project itself contains
// tests and examples of the actual standard library code.

module UsesWrappers {

  import opened Std.Wrappers

  function SafeDiv(a: int, b: int): Option<int> {
    if b == 0 then None else Some(a/b)
  }

  method Main() {
    print SafeDiv(4, 2), "\n";
    print SafeDiv(7, 0), "\n";
  }
}
