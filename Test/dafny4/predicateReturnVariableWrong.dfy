// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
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

type MyBoolSynonym = bool

predicate tautology1(x: int): (y: MyBoolSynonym) {
  true
}

type AlwaysTrue = x: bool | x

predicate tautology1(x: int): (y: AlwaysTrue) {
  true
}
