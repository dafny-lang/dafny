// RUN: %testDafnyForEachResolver "%s"


datatype T = T1(x:nat) | T2(y:nat) {
    ghost predicate i() requires T2? {
        y > 0
    }
}

