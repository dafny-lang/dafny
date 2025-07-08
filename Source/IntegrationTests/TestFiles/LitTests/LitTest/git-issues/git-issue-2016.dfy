// RUN: %testDafnyForEachResolver "%s"


module M {
  datatype D = D() {
    static function f(): (res: int) {
      5
    } by method {
      return 5;
    }
  }
}
