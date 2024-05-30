// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function CanUnderflow(c0: char, c1: char): char {
    c0 - c1
}