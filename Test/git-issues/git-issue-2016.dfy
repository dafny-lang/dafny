// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  datatype D = D() {
    static function f(): (res: int) {
      5
    } by method {
      return 5;
    }
  }
}
