// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype DT = C(s: string) {
  ghost predicate F() {
    C.XYZ()
  }
}
