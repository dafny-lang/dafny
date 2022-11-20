// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype DT = C(s: string) {
  predicate F() {
    C.XYZ()
  }
}