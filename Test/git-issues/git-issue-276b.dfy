// RUN: %dafny /compile:0 /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Main {
    const A := B + 1
    const B := A - 1
    newtype b1 = x | 0 <= x < A
}

