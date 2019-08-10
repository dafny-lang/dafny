// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "./NatOutcome.dfy"

method Switch(b: bool, v: nat) returns (res: NatOutcome) {
    if b {
        res := MakeNatSuccess(v);
    } else {
        res := MakeNatFailure("bad luck");
    }
}

method TestControlFlowCase(switch1: bool, switch2: bool, switch3: bool) returns (res: NatOutcome) {
    print switch1, "_", switch2, "_", switch3, "_";
    var n1 :- Switch(switch1, 88);
    print n1, "_";
    var n2: nat :- Switch(switch2, 42);
    print n2, "_";
    n1 :- Switch(switch3, 33);
    print n1, "_";
    res := MakeNatSuccess(100);
}

method TestControlFlow() {
    var i: nat := 0;
    while i < 8 {
        var materialized: NatOutcome := TestControlFlowCase(i / 4 % 2 == 0, i / 2 % 2 == 0, i % 2 == 0);
        if materialized.IsFailure() {
            print "Failure\n";
        } else {
            print "Success=", materialized.Extract(), "\n";
        }
        i := i + 1;
    }
}

method TestParsing(b: bool, n: nat, o1: NatOutcome, o2: NatOutcome) returns (res: NatOutcome) {
    // 2x2 matrix of (expr, stmt) x (explicit type, no explicit type), where stmt also tests reassignment

    var stmt1: nat :- MakeNatSuccess(n);
    stmt1 :- MakeNatFailure("sorry, bad luck");
    var use_stmt1: nat := stmt1;

    var stmt2 :- MakeNatSuccess(n);
    stmt2 :- MakeNatFailure("sorry, bad luck");
    var use_stmt2: nat := stmt2;

    /* expected to desugar to something like this:
    var y: nat;
    var temp := o1; if temp.IsFailure() { return temp.PropagateFailure(); } y := temp.Extract();
    */
    
    return o1;
}

/*
method TestParsing(b: bool, n: nat, o1: NatOutcome, o2: NatOutcome) {
    // 2x2 matrix of (expr, stmt) x (explicit type, no explicit type), where stmt also tests reassignment

    var expr1: nat :- (var x := if b then o1 else o2; x);
    var use_expr1: nat := expr1;

    var stmt1: nat :- MakeNatSuccess(n);
    stmt1 :- MakeNatFailure("sorry, bad luck");
    var use_stmt1: nat := stmt1;

    var expr2 :- (var x := if b then o1 else o2; x);
    var use_expr2: nat := expr2;

    var stmt2 :- MakeNatSuccess(n);
    stmt2 :- MakeNatFailure("sorry, bad luck");
    var use_stmt2: nat := stmt2;
}
*/

method Main() {
    TestControlFlow();
}
