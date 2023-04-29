
// Ensuring the compatibility checks are also run when including a .doo file.
// Also ensures a checked-in .doo file continues to work as Dafny evolves.

// RUN: %baredafny verify %args --unicode-char:true %s > %t
// RUN: ! %baredafny verify %args --unicode-char:false %s >> %t
// Using OutputCheck because the include error uses absolute file paths
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-NEXT-LITERAL: Dafny program verifier finished with 0 verified, 0 errors
// CHECK: Error: Cannot load .*wrappers3.doo: --unicode-char is set locally to False, but the library was built with True
// CHECK-NEXT-LITERAL: Include of file "wrappers3.doo" failed.

include "wrappers3.doo"

module UsesWrappers {

  import opened Wrappers

  function Maybe(): Option<int> {
    Some(42)
  }
}
