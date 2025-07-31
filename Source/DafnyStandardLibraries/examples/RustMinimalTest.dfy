/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// Minimal test to verify Rust standard library works without ORDINAL errors
module RustMinimalTest {
  import opened Std.Wrappers

  @Test
  method TestBasicFunctionality() {
    // Test basic wrapper functionality
    var result: Result<int, string> := Success(42);
    expect result.Success?;
    expect result.value == 42;
    
    var failure: Result<int, string> := Failure("error");
    expect failure.Failure?;
    expect failure.error == "error";
    
    print "Rust standard library basic test: PASSED\n";
  }
}
