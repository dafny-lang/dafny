// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate tautology1(x: int): (y: int) {
  true
}

least predicate tautology2(x: int): (y: int) {
  true
}

greatest predicate tautology3(x: int): (y: int) {
  true
}