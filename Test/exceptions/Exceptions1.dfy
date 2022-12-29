// RUN: %baredafny run %args "%s" /rprint:"%t.rprint" > "%t"
// RUN: %diff "%s.expect" "%t"
include "./NatOutcome.dfy"
include "./VoidOutcome.dfy"

method Switch(b: bool, v: nat) returns (res: NatOutcome) {
    if b {
        res := MakeNatSuccess(v);
    } else {
        res := MakeNatFailure("bad luck");
    }
}

method TestControlFlowCase_Nat(switch1: bool, switch2: bool, switch3: bool) returns (res: NatOutcome) {
    var n1 :- Switch(switch1, 88);
    print n1, "_";
    var n2: nat :- Switch(switch2, 42);
    print n2, "_";
    n1 :- Switch(switch3, 33);
    print n1, "_";
    res := MakeNatSuccess(100);
}

method FailIf(b: bool) returns (res: VoidOutcome) {
    if b {
        res := MakeVoidSuccess();
    } else {
        res := MakeVoidFailure("void bad luck");
    }
}

method TestControlFlowCase_Void(switch1: bool, switch2: bool, switch3: bool) returns (res: VoidOutcome) {
    :- FailIf(switch1);
    print "_";
    :- FailIf(switch2);
    print "_";
    :- FailIf(switch3);
    print "_";
    res := MakeVoidSuccess();
}

method TestControlFlow() {
    var i: nat := 0;
    while i < 8 {
        var switch1, switch2, switch3 := i / 4 % 2 == 0, i / 2 % 2 == 0, i % 2 == 0;
        print switch1, "_", switch2, "_", switch3, "_";

        var materialized1: NatOutcome := TestControlFlowCase_Nat(switch1, switch2, switch3);
        if materialized1.IsFailure() {
            print "Failure\n";
        } else {
            print "Success=", materialized1.Extract(), "\n";
        }

        var materialized2: VoidOutcome := TestControlFlowCase_Void(switch1, switch2, switch3);
        if materialized2.IsFailure() {
            print "VoidFailure\n";
        } else {
            print "VoidSuccess\n";
        }

        i := i + 1;
    }
}

method TestStatementParsing(b: bool, n: nat, o1: NatOutcome, o2: NatOutcome) returns (res: NatOutcome) {
    // 2x2 matrix of (rhs is expr, rhs is method call) x (explicit type, no explicit type), where stmt also tests reassignment

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

    return o1;
}

method Main() {
    TestControlFlow();
}
