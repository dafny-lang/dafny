// RUN: %dafny /compile:0 /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Main {
    newtype b1 = x | 0 <= x < 3/(2-2)
    newtype b2 = x | 0 <= x < 3%(2-2)
}

