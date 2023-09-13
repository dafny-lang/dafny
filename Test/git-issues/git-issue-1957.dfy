// RUN: %dafny /compile:0 /printTooltips "%s" > "%t"


class {:autocontracts} Thing {
    ghost predicate Valid() {
        true
    }
}
