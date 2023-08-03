include "AlcorEngine.dfy"
module AlcorEngineTest {
  import opened AlcorProofKernel
  import opened Alcor

  method {:test} DummyProofFinderTest() {
    print "\n";
    var ia := Identifier("a");
    var ib := Identifier("b");
    var ic := Identifier("c");
    var id := Identifier("d");
    var a := Var(ia);
    var b := Var(ib);
    var c := Var(ic);
    var d := Var(id);
    var remaining := Var(Identifier("remaining"));
    
    var goal := Imp(And(And(a, b), remaining), a);
    var expr :- expect DummyProofFinder(goal);
    print "Automatically found a proof of " + goal.ToString() + "\n";

    goal := Imp(And(And(a, b), remaining), b);
    expr :- expect DummyProofFinder(goal);
    print "Automatically found a proof of " + goal.ToString() + "\n";

    goal := Imp(And(a, And(b, And(c, And(d, remaining)))), d);
    expr :- expect DummyProofFinder(goal);
    print "Automatically found a proof of " + goal.ToString() + "\n";

    
    goal := Imp(remaining, Imp(b, b));
    expr :- expect DummyProofFinder(goal);
    print "Automatically found a proof of " + goal.ToString() + "\n";

    goal := Imp(remaining, Imp(And(a, b), b));
    expr :- expect DummyProofFinder(goal);
    print "Automatically found a proof of " + goal.ToString() + "\n";

    goal := Imp(And(Imp(a, b), And(a, True)), b);
    expr :- expect DummyProofFinder(goal);
    print "Automatically found a proof of " + goal.ToString() + "\n";

    goal := Imp(And(a, And(Imp(a, b), True)), b);
    expr :- expect DummyProofFinder(goal);
    print "Automatically found a proof of " + goal.ToString() + "\n";

    goal := Imp(And(a, And(b, remaining)), And(a, b));
    expr :- expect DummyProofFinder(goal);
    print "Automatically found a proof of " + goal.ToString() + "\n";

    goal := Imp(And(b, And(a, remaining)), And(a, b));
    expr :- expect DummyProofFinder(goal);
    print "Automatically found a proof of " + goal.ToString() + "\n";
  }

  method {:test} ProofCheckerTest() {
    print "\n";
    var ia := Identifier("a");
    var ib := Identifier("b");
    var a := Var(ia);
    var b := Var(ib);
    
    var goal := Forall(Abs(ia,
                Forall(Abs(ib, Imp(And(Imp(a, b), a), And(b, a))))));

    var proofProgram :=
          ForallIntro.apply2(ProofExpr(a),
            ForallIntro.apply2(ProofExpr(b),
              ImpIntro.apply2(
                ProofExpr(And(Imp(a, b), a)),
                ProofAbs("env", Ind,
                  Let("a", Ind, AndElimRight.apply1(ProofVar("env")),
                  Let("aToB", Ind, AndElimLeft.apply1(ProofVar("env")),
                  Let("b", Ind, ImpElim.apply2(ProofVar("aToB"), ProofVar("a")),
                  AndIntro.apply2(ProofVar("b"), ProofVar("a")))))))));
    var result :- expect CheckProof(proofProgram, EnvNil, goal);

  }
}









