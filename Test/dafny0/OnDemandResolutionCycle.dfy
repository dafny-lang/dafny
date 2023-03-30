// RUN: %exits-with 2 %dafny /compile:0 /typeSystemRefresh:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type A = x | x == a // error: cycle
const a: A := 2

type B = x | x == FB() // error: cycle
const b := FB()
function FB(): B

const c0 := c1 // error: cycle
const c1 := c0

newtype D = x | x == d // error: cycle
const d: D := 2

newtype E = x | x == FE() // error: cycle
const e := FE()
function FE(): E

newtype F = x | x == f()
function f(): F
