// RUN: %exits-with 2 %dafny /compile:0 /typeSystemRefresh:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type A = x | x == a
const a: A := 2
