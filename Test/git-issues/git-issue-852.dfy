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

