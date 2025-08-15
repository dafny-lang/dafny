/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// Simple test to verify coercion fixes work
module SimpleTest {
  import opened Std.Wrappers

  method {:main} Main() {
    var result: Result<int, string> := Success(42);
    match result {
      case Success(value) => {
        print "Success: ", value, "\n";
        print "Simple test: PASSED\n";
      }
      case Failure(error) => {
        print "Failure: ", error, "\n";
        print "Simple test: FAILED\n";
      }
    }
  }
}
