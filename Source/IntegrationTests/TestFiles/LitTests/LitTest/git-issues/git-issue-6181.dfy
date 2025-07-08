// RUN: %testDafnyForEachResolver "%s"

trait Number extends object { }
class Integer extends Number { }

method M(i: Integer, j: Integer) returns (r: bool) {
    var a: (Number, Integer) := (i, j);
    var b: (Integer, Number) := (i, j);
    return a == b;
}
