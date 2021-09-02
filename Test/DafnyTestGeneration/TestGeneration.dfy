// RUN: %dafny /definiteAssignment:3 /generateTestMode:Block TestGeneration.dfy > %t.raw
// RUN: sed 's/[1-9][0-9]*/INT/g' %t.raw > %t
// RUN: %diff "%s.expect" "%t"

module M {
    class Value {
        var v:int;
    }
    method compareToZero(v:Value) returns (i:int) {
        if (v.v == 0) {
            return 0;
        } else if (v.v > 0) {
            return 1;
        }
        return -1;
    }
}
