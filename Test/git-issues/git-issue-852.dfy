// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module M0 {
    newtype T = n:nat | true {
        predicate p() {true}
    }
}
module Q refines M0 {
    newtype T = n:nat | true {
        predicate p() {true}
    }
}

