include "AlcorEngine.dfy"
module AlcorEngineTest {
  import opened AlcorProofKernel
  import opened Alcor
  import opened AlcorTacticProofChecker

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
    var result :- expect CheckProof(proofProgram, ProofEnvNil, goal);
  }

  
  method {:test} TacticProofCheckerTest() {
    print "\n";
    var ia := Identifier("a");
    var ib := Identifier("b");
    var a := Var(ia);
    var b := Var(ib);
    
    var goal := Forall(Abs(ia,
                Forall(Abs(ib, Imp(And(Imp(a, b), a), And(b, a))))));

    var thinking := new TacticMode(goal, EnvNil);
    expect thinking.proofState.ToString() == "\n|- forall a :: (forall b :: (a ==> b) && a ==> b && a)";
    var feedback :- expect thinking.Intro();
    print feedback, "\n--------------\n";
    expect feedback == "\n|- forall b :: (a ==> b) && a ==> b && a";
    feedback :- expect thinking.Intro();
    print feedback, "\n--------------\n";
    expect feedback == "\n|- (a ==> b) && a ==> b && a";
    feedback :- expect thinking.Intro("h");
    print feedback, "\n--------------\n";
    expect feedback == "h: (a ==> b) && a\n|- b && a";
    feedback :- expect thinking.Rename(Identifier("h"), Identifier("hA"));
    print feedback, "\n--------------\n";
    expect feedback == "hA: (a ==> b) && a\n|- b && a";
    feedback :- expect thinking.Cases();
    print feedback, "\n--------------\n";
    expect feedback == "hA: (a ==> b) && a\n|- b\n\nhA: (a ==> b) && a\n|- b ==> a";
    feedback :- expect thinking.CasesEnv("hA", "hAB", "hA");
    print feedback, "\n--------------\n";
    expect feedback == "hAB: a ==> b\nhA: a\n|- b\n\nhA: (a ==> b) && a\n|- b ==> a";
    feedback :- expect thinking.ImpElim("hAB", "hA");
    print feedback, "\n--------------\n";
    expect feedback == "hA: (a ==> b) && a\n|- b ==> a";
    feedback :- expect thinking.CasesEnv("hA", "hAB", "hA");
    print feedback, "\n--------------\n";
    expect feedback == "hAB: a ==> b\nhA: a\n|- b ==> a";
    feedback :- expect thinking.Intro("hB");
    print feedback, "\n--------------\n";
    expect feedback == "hB: b\nhAB: a ==> b\nhA: a\n|- a";
    feedback :- expect thinking.UseHypothesis("hA");
    print feedback, "\n--------------\n";
    expect feedback == "";
    
    // thinking.ImpElim(hAB, hA)
    print "\n";
  }
}









