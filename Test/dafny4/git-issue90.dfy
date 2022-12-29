// RUN: %exits-with 2 %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const x: MyInt := 200
const y: int := x as int + 180
newtype MyInt = k | 0 <= k < y


