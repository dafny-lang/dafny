// RUN: %baredafny run %args "%s" /rprint:"%t.rprint" > "%t"
// RUN: %diff "%s.expect" "%t"
include "./NatOutcomeDt.dfy"
include "./VoidOutcomeDt.dfy"

function method Switch(b: bool, v: nat): NatOutcome {
    if b then NatSuccess(v) else NatFailure("bad luck")
}

function method TestControlFlowCase_Nat(switch1: bool, switch2: bool, switch3: bool): NatOutcome {
    var n1 :- Switch(switch1, 88);
    var n2: nat :- Switch(switch2, 42);
    var n1 :- Switch(switch3, 33);
    NatSuccess(100)
}

function method FailIf(b: bool): VoidOutcome {
    if b then VoidSuccess() else VoidFailure("void bad luck")
}

function method TestControlFlowCase_Void(switch1: bool, switch2: bool, switch3: bool): VoidOutcome {
    :- FailIf(switch1);
    :- FailIf(switch2);
    :- FailIf(switch3);
    VoidSuccess()
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

function TestExpressionParsing(b: bool, n: nat, o1: NatOutcome, o2: NatOutcome): NatOutcome {
    var expr1: nat :- (var x := if b then o1 else o2; x);
    var use_expr1: nat := expr1;
    var expr2 :- (var x := if b then o1 else o2; x);
    var use_expr2: nat := expr2;
    o2
}

method Main() {
    TestControlFlow();
}
