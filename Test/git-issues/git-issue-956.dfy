// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype T = T1(x:nat) | T2(y:nat) {
    predicate i() requires T2? {
        y > 0
    }
}

