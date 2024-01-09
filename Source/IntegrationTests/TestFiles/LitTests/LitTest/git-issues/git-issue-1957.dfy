// RUN: %verify --show-inference "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class {:autocontracts} Thing {
    ghost predicate Valid() {
        true
    }
}
