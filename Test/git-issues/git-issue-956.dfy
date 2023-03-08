// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype T = T1(x:nat) | T2(y:nat) {
    ghost predicate i() requires T2? {
        y > 0
    }
}

