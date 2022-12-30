// RUN: %baredafny verify %args --print-tooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class {:autocontracts} Thing {
    predicate Valid() {
        true
    }
}
