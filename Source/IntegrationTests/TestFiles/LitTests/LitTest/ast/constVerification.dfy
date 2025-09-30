// RUN: ! %verify --allow-axioms=false --general-traits=datatype --type-system-refresh --general-newtypes "%s" > %t
// RUN: %diff "%s.expect" "%t"

type Even = x: int | x % 2 == 0
opaque const ten: Even := 10

trait T {}
datatype Crazy extends T = Crazy() {}
const d: T := Crazy()