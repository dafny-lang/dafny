include "AlcorEngine.dfy"
module AlcorEngineTest {
  import opened AlcorProofKernel
  import opened Alcor

  method {:test} DummyProofFinderTest() {
    print "\n";
    
    var goal := Imp(And(And(Var("a"), Var("b")), Var("...")), Var("a"));
    var expr :- expect DummyProofFinder(goal);
    print "Automatically found a proof of " + goal.ToString() + "\n";

    goal := Imp(And(And(Var("a"), Var("b")), Var("...")), Var("b"));
    expr :- expect DummyProofFinder(goal);
    print "Automatically found a proof of " + goal.ToString() + "\n";

    goal := Imp(And(Var("a"), And(Var("b"), And(Var("c"), And(Var("d"), Var("..."))))), Var("d"));
    expr :- expect DummyProofFinder(goal);
    print "Automatically found a proof of " + goal.ToString() + "\n";

    
    goal := Imp(Var("..."), Imp(Var("b"), Var("b")));
    expr :- expect DummyProofFinder(goal);
    print "Automatically found a proof of " + goal.ToString() + "\n";

    goal := Imp(Var("..."), Imp(And(Var("a"), Var("b")), Var("b")));
    expr :- expect DummyProofFinder(goal);
    print "Automatically found a proof of " + goal.ToString() + "\n";

    goal := Imp(And(Imp(Var("a"), Var("b")), And(Var("a"), True)), Var("b"));
    expr :- expect DummyProofFinder(goal);
    print "Automatically found a proof of " + goal.ToString() + "\n";

    goal := Imp(And(Var("a"), And(Imp(Var("a"), Var("b")), True)), Var("b"));
    expr :- expect DummyProofFinder(goal);
    print "Automatically found a proof of " + goal.ToString() + "\n";

    goal := Imp(And(Var("a"), And(Var("b"), Var("..."))), And(Var("a"), Var("b")));
    expr :- expect DummyProofFinder(goal);
    print "Automatically found a proof of " + goal.ToString() + "\n";

    goal := Imp(And(Var("b"), And(Var("a"), Var("..."))), And(Var("a"), Var("b")));
    expr :- expect DummyProofFinder(goal);
    print "Automatically found a proof of " + goal.ToString() + "\n";
  }
}