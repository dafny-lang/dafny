// Regression test for including the standard libraries in a doo file.
// This used to break because we incorrectly required --standard-libraries to be set when consuming too,
// which led to duplicate definitions.

// RUN: %build %s -t:lib --standard-libraries:true --output="%S/Output/useStandardLibraries.doo" &> "%t"
// RUN: %run %S/Output/useStandardLibraries.doo &>> %t
// RUN: %diff "%s.expect" "%t"

import opened Std.Wrappers
import opened Std.Collections.Seq

method Main() {
  print IndexOfOption([1, 1, 2, 3, 5, 8, 13, 21], 5), "\n";
}