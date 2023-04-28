
// Ensuring the compatibility checks are also run when including a .doo file.
// Also ensures a checked-in .doo file continues to work as Dafny evolves.

// RUN: %verify --unicode-char:true %s > %t
// RUN: ! %verify --unicode-char:false %s >> %t
// RUN: %diff "%s.expect" %t

include "wrappers3.doo"

module UsesWrappers {

  import opened Wrappers

  function Maybe(): Option<int> {
    Some(42)
  }
}
