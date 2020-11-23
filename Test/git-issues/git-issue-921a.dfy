// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module StringsOfLength {
  type ShortString = s: string | |s| <= 2

  method M() {
    var x2: ShortString := "12" + "34"; // no error!
  }
}
