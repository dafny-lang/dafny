// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module M0 {
  newtype T = n:nat | true {
    ghost predicate p() {true}
  }
}

module Q0 refines M0 {
  newtype T = n:nat | true {  // error: needs ...
    ghost predicate p() {true}
  }
}

module Q1 refines M0 {
  newtype T ... {
    ghost predicate p() {true}  // error: p() already has a body in M0
  }
}

module Q2 refines M0 {
  newtype T ... {
    ghost predicate p... {true}  // error: p() already has a body in M0
  }
}

module Q3 refines M0 {
  newtype T ... {
    ghost predicate p...  // allowed (but what's the point?)
  }
}
