// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost predicate tautology1(x: int): (y: int) {
  true
}

least predicate tautology2(x: int): (y: int) {
  true
}

greatest predicate tautology3(x: int): (y: int) {
  true
}

type MyBoolSynonym = bool

ghost predicate tautology1(x: int): (y: MyBoolSynonym) {
  true
}

type AlwaysTrue = x: bool | x

ghost predicate tautology1(x: int): (y: AlwaysTrue) {
  true
}
