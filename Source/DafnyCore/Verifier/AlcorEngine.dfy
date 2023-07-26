// TODO: Use AutoExtern to convert Dafny's expressions into Alcor's language
module Wrappers {
  
  datatype Result<S> = Success(value: S) | Failure(msg: string)
  {
    function Map<T>(f: S -> T): Result<T> {
      if Success? then Success(f(value)) else Failure(msg)
    }
    predicate IsFailure() {
      Failure?
    }
    function PropagateFailure<U>(): Result<U>
      requires IsFailure()
    {
      Failure(msg)
    }
    function Extract(): S
      requires !IsFailure()
    {
      value
    }
  }

  function IntToString(i: int): string
    decreases if i < 0 then 1-i else i
  {
    if i < 0 then "-" + IntToString(-i) else
    var unit :=  ["0123456789"[i % 10]];
    if i <= 9 then unit else IntToString(i/10) + unit
    }
}

module AlcorProofKernel {
  import opened Wrappers
// We provide ways for external users to create exprs and a proof.
  // Alcor can run the proof to see if it obtains an expe
  export provides Proof, Proof.GetExpr
         provides Proof.AndIntro, Proof.AndElimLeft, Proof.AndElimRight
         provides Proof.ImpElim, Proof.ImpIntro
         provides Wrappers, Expr.ToString
         reveals Expr, Expr.Not

  // TODO: Intermediate language for Dafny, including references, sets, etc.
  datatype Expr =
    | True
    | False
    | And(left: Expr, right: Expr)
    | Imp(left: Expr, right: Expr)
    | Eq(left: Expr, right: Expr) // Same as Iff but for everything
    | Or(left: Expr, right: Expr)
    | Var(name: string, version: nat := 0, lbl: string := "")
    | Abs(name: string, body: Expr)
    | App(left: Expr, right: Expr)
    | Forall(body: Expr) // Typically an Abs, but can be a name
  {
    static function Not(expr: Expr): Expr {
      Imp(expr, False)
    }

    function Operator(): string
    {
      if And? then "&&" else
      if Or? then "||" else
      if Imp? then "==>" else
      //if Iff? then "<==>" else
      if Eq? then "==" else
      if False? then "false" else
      if True? then "true" else
      if Var? then
      name
      + (if lbl != "" then "@" + lbl else "")
      + (if version == 0 then "" else "@" + IntToString(version))
      else ""
    }
    function ToStringWrap(outerPriority: nat): string
      decreases this, 1
    {
      var r := ToString();
      if outerPriority >= Priority() then
        "(" + r + ")"
      else
        r
    }
    function Priority(): nat {
      if False? || True? || Var? then 10
      else if Eq? then 9
      else if And? then 8
      else if Or? then 7
      else if Imp? then if right.False? then 10 else 6
      else if Abs? then 5 else if App? then 5
      else if Forall? then 4
      //else if Iff? then 1
      else 0
    }
    function ToString(): string
      decreases this, 0
    {
      var p := Priority();
      if Imp? && right.False? then "!" + left.ToStringWrap(p)
      else if And? || Or? || /*Iff? ||*/ Eq? || Imp? then
        left.ToStringWrap(p) + " "+Operator()+" " + right.ToStringWrap(p)
      else if Abs? then
        "\\" + name + "." + body.ToStringWrap(p + 1)
      else if App? then
        left.ToStringWrap(p) + " " + right.ToStringWrap(p)
      else if Forall? then
        "forall " + body.ToStringWrap(p + 1)
      else
      Operator()
    }
  }

  datatype Proof = Proof(expr: Expr)
  {
    function GetExpr(): Expr {
      expr
    }

    function and(other: Proof): Result<Proof> {
      AndIntro(this, other)
    }

    // Everything below must be carefully checked
    // Logic axioms
    static function AndIntro(left: Proof, right: Proof): Result<Proof> {
      Success(Proof(And(left.expr, right.expr)))
    }
    static function AndElimLeft(elem: Proof): Result<Proof> {
      if !elem.expr.And? then
        Failure("To apply AndElimLeft, expected And(), got " + elem.expr.ToString())
      else
        Success(Proof(elem.expr.left))
    }
    static function AndElimRight(elem: Proof): Result<Proof> {
      if !elem.expr.And? then
        Failure("To apply AndElimRight, expected And(), got " + elem.expr.ToString())
      else
        Success(Proof(elem.expr.right))
    }
    static function ImpElim(aToB: Proof, a: Proof): Result<Proof> {
      if !aToB.expr.Imp? then
        Failure("To apply ImpElim, the first argument must be ==>, got " +aToB.expr.ToString())
      else if aToB.expr.left != a.expr then
        Failure("To apply ImpElim, the second argument must be the hypothesis of the first one. But got " + aToB.expr.ToString() + " and " + a.expr.ToString())
      else
        assert aToB.expr.Imp? && aToB.expr.left == a.expr;
        Success(Proof(aToB.expr.right))
    }
    // The fact that hypothesis is a pure function prevents anything to store the temporary proof object this function provides
    static function ImpIntro(hypothesis: Expr, pHypothesis: Proof -> Result<Proof>): Result<Proof> {
      var p := Proof(hypothesis);
      var result :- pHypothesis(p);
      Success(Proof(Imp(hypothesis, result.expr)))
    }
  }
}


module Alcor {
  import opened Wrappers
  import opened AlcorProofKernel
  

  datatype Environment =
    | EnvNil
    | EnvCons(name: string, value: ProofValue, tail: Environment)
  {
    function Lookup(searchName: string): Result<ProofValue> {
      if EnvNil? then Failure("Did not find "+searchName+" in the proof environment")
      else if name == searchName then
        Success(value)
      else
        tail.Lookup(searchName)
    }
  }

  // We carefully add proof axioms here
  datatype ProofAxiom =
    | AndIntro
    | AndElimLeft
    | AndElimRight
    | ImpElim
    | ImpIntro
  {
    function apply1(A: ProofProgram): ProofProgram {
      ProofProgram.ProofAxiom(this).apply1(A)
    }
    function apply2(A: ProofProgram, B: ProofProgram): ProofProgram {
      ProofProgram.ProofAxiom(this).apply2(A, B)
    }
    function ToString(): string {
      match this
      case AndIntro => "AndIntro"
      case AndElimLeft => "AndElimLeft"
      case AndElimRight => "AndElimRight"
      case ImpElim => "ImpElim"
      case ImpIntro => "ImpIntro"
    }
    function Arity(): nat {
      match this {
        case AndIntro => 2
        case AndElimLeft => 1
        case AndElimRight => 1
        case ImpIntro => 2
        case ImpElim => 2
      }
    }
    function ExtractProof(args: seq<ProofValue>, i: nat): Result<Proof>
      requires 0 <= i < |args|
    {
      var arg := args[i];
      if arg.OneProof? then
        Success(arg.proof)
      else
        Failure("At index " + IntToString(i) + " of " + ToString() + ", expected proof, but got " + arg.Summary())
    }
    function ExtractExpr(args: seq<ProofValue>, i: nat): Result<Expr>
      requires 0 <= i < |args|
    {
      var arg := args[i];
      if arg.OneExpr? then
        Success(arg.expr)
      else
        Failure("At index " + IntToString(i) + " of " + ToString() + ", expected expr, but got " + arg.Summary())
    }
    function {:fuel 30, 30} ApplyArgs(ghost program: ProofProgram, args: seq<ProofValue>, environment: Environment): Result<ProofValue>
      requires |args| == Arity()
      decreases DecreasesStep(program), 0
    {
      //var _ := Debug("ApplyArgs(" + ToString() + ", " + IntToString(Arity()) + ")\n");
      match this {
        case AndIntro =>
          var left :- ExtractProof(args, 0);
          var right :- ExtractProof(args, 1);
          Proof.AndIntro(left, right).Map(p => OneProof(p))
        case AndElimLeft =>
          var elem :- ExtractProof(args, 0);
          Proof.AndElimLeft(elem).Map(p => OneProof(p))
        case AndElimRight =>
          var elem :- ExtractProof(args, 0);
          Proof.AndElimRight(elem).Map(p => OneProof(p))
        case ImpIntro =>
          var hypothesis :- ExtractExpr(args, 0);
          var reasoning := args[1];
          if !reasoning.OneClosure? then
            Failure("Second argument of ImpIntro requires a closure, got " + reasoning.Summary())
          else
            var argName := reasoning.argName;
            var body := reasoning.body;
            assert reasoning.OneClosure?;
            var proofBuilder: Proof -> Result<Proof> := (p: Proof) =>
              assume {:axiom} DecreasesStep(body) < DecreasesStep(program);
              var x :- ExecuteProof(body, EnvCons(argName, OneProof(p), environment));
              if x.OneProof? then Success(x.proof)
              else Failure("Closure should return a proof, but got " + x.Summary());
            Proof.ImpIntro(hypothesis, proofBuilder).Map(p => OneProof(p))
        case ImpElim =>
          var left :- ExtractProof(args, 0);
          var right :- ExtractProof(args, 1);
          Proof.ImpElim(left, right).Map(p => OneProof(p))
      }
    }
  }


  // Individuals
  datatype Type = Ind | Bool | Arrow(Type, Type)
   // Should be a program in simply typed lampda calculus + proof primitives
  datatype ProofProgram =
    | ProofVar(name: string) // Represents
    | ProofExpr(expr: Expr)
    | ProofAbs(name: string, tpe: Type, body: ProofProgram)
    | ProofApp(left: ProofProgram, right: ProofProgram)
    | ProofAxiom(axiom: ProofAxiom)
  {
    function apply1(A: ProofProgram): ProofProgram {
      ProofApp(this, A)
    }
    function apply2(A: ProofProgram, B: ProofProgram): ProofProgram {
      ProofApp(ProofApp(this, A), B)
    }
    function ToString(): string {
      match this
      case ProofVar(name) => name
      case ProofAbs(name, tpe, body) => "(\\"+name+". "+body.ToString()+")"
      case ProofApp(left, right) => left.ToString() + "(" + right.ToString() + ")"
      case ProofAxiom(axiom) => axiom.ToString()
      case ProofExpr(expr) => "``" + expr.ToString() + "``"
    }
  }
  
  function Let(name: string, tpe: Type, expression: ProofProgram, body: ProofProgram): ProofProgram {
    ProofApp(ProofAbs(name, tpe, body), expression)
  }
  
  datatype ProofValue =
    | OneProof(proof: Proof)
    | OneExpr(expr: Expr)
    | OneClosure(argName: string, tpe: Type, body: ProofProgram, environment: Environment)
    | OneClosureAxiom(args: seq<ProofValue>, axiom: ProofAxiom)
  {
    function Summary(): string {
      if OneProof? then "proof"
      else if OneClosure? then "proof closure" // TODO of typo
      else if OneExpr? then "expr"
      else "incomplete axiom instantiation"
    }
  }



  //predicate SimplyTyped(program: ProofProgram)

  ghost function {:axiom} DecreasesStep(program: ProofProgram): nat

  function Debug(msg: string): int {
    0
  } by method {
    print msg;
    return 0;
  }

  // A call-by-value proof program should be guaranteed to terminate by construction
  function {:fuel 30, 30} ExecuteProof(program: ProofProgram, environment: Environment): Result<ProofValue>
    //requires SimplyTyped(program)
    decreases DecreasesStep(program), 1
  {
    //var _ := Debug("ExecuteProof(" + program.ToString() + ")\n");
    match program {
      case ProofVar(name) =>
        environment.Lookup(name)
      case ProofExpr(expr) =>
        Success(OneExpr(expr))
      case ProofAbs(name, tpe, body) =>
        Success(OneClosure(name, tpe, body, environment))
      case ProofAxiom(axiom) =>
        Success(OneClosureAxiom([], axiom))
      case ProofApp(left, right) =>
        assume {:axiom} DecreasesStep(left) < DecreasesStep(program);
        var result :- ExecuteProof(left, environment);
        if result.OneClosure? then
          assume {:axiom} DecreasesStep(right) < DecreasesStep(program);
          var argument :- ExecuteProof(right, environment);
          assume {:axiom} DecreasesStep(result.body) < DecreasesStep(program);
          ExecuteProof(result.body, EnvCons(result.argName, argument, result.environment))
        else if result.OneClosureAxiom? then
          assume {:axiom} DecreasesStep(right) < DecreasesStep(program);
          var argument :- ExecuteProof(right, environment);
          if result.axiom.Arity() == |result.args| + 1 then
            result.axiom.ApplyArgs(program, result.args + [argument], environment)
          else
            Success(OneClosureAxiom(result.args + [argument], result.axiom))
        else
          Failure("Left of application was not a closure")
    }
  }

  // Should be the main API
  function CheckProof(program: ProofProgram, environment: Environment, expected: Expr): Result<Proof> {
    var result :- ExecuteProof(program, environment);
    if result.OneClosure? || result.OneClosureAxiom? then
      Failure("Expected a proof of " + expected.ToString() + ", got a closure proof")
    else if result.OneExpr? then
      Failure("Expected a proof of " + expected.ToString() + ", got a simple expression")
    else if result.proof.GetExpr() != expected then
      Failure("Expected a proof of " + expected.ToString() + " but got a proof of " + result.proof.GetExpr().ToString())
    else
      Success(result.proof)
  }

  ghost function numberOfImp(expr: Expr): nat {
    if expr.Imp? then numberOfImp(expr.right) + 1 else 0
  }

  opaque function checkGoalAgainstExpr(pv: ProofValue, expr: Expr): (result: Result<Proof>)
    ensures result.Success? ==> result.value.GetExpr() == expr
  {
    if !pv.OneProof? then Failure("DummyProofFinder did not generate a proof but " + pv.Summary()) else
      var p := pv.proof;
      if p.GetExpr() == expr then Success(p) else
      Failure("DummyProofFinder was looking for a proof of " + expr.ToString() + " but returned a proof of " + p.GetExpr().ToString())
  }

  // No need to trust this proof finder, if it finds a proof it's a correct one!
  method DummyProofFinder(expr: Expr)
    returns (result: Result<Proof>)
    decreases if expr.Imp? then numberOfImp(expr.right) else 0
    ensures result.Success? ==> result.value.GetExpr() == expr
  {
    var checkGoal: ProofValue -> Result<Proof> := (pv: ProofValue) => checkGoalAgainstExpr(pv, expr);
    // Given an expression (A0 && (A1 && (A2 && .... True))) ==> G
    // Will try to find a proof of it.
    // * If A1 is (a && b) and G is b, we emit the proof
    // * If A1 is a and A0 is b and G is a && b, we emit the proof
    // * If A1 is (a ==> b) and A0 is a and G is b, we emit the proof.
    if !expr.Imp? {
      return Failure("ProofFinder requires an implication");
    }
    var goal := expr.right;
    var env := expr.left;
    if goal.Imp? {
      // Let's put the hypothesis in the environment and prove it.
      var proofOfConclusion := DummyProofFinder(Imp(And(goal.left, env), goal.right));
      if proofOfConclusion.Success? {
        // We have a proof that A && env ==> B
        // Now let's transform it in a proof of env ==> (A ==> B)
        var execEnv := EnvCons("a_x_imp_b", OneProof(proofOfConclusion.value), EnvNil);
        var r :- ExecuteProof(
          ImpIntro.apply2(
            ProofExpr(env),
            ProofAbs("env", Ind,
              ImpIntro.apply2(
                ProofExpr(goal.left),
                ProofAbs("proofOfA", Ind,
                  ImpElim.apply2(
                    ProofVar("a_x_imp_b"),
                    AndIntro.apply2(
                      ProofVar("proofOfA"),
                      ProofVar("env"))))))), execEnv);
        return checkGoal(r);
      }
    }
    // The and separating the head of the environment to the tail
    if !env.And? {
      return Failure("ProofFinder requires an environment to the left of ==>");
    }
    var A0 := env.left;
    var tail := env.right;
    // * if A0 is (a && b) and G is a, we emit the proof
    if A0.And? {
      if A0.left == goal {
        // Let's build a proof
        var proofProgram :=
          ImpIntro.apply2(
            ProofExpr(env),
            ProofAbs("env", Ind, 
              AndElimLeft.apply1(
                 AndElimLeft.apply1(ProofVar("env")))
            ));
        var r :- ExecuteProof(proofProgram, EnvNil);
        return checkGoal(r);
      }
      if A0.right == goal {
        var proofProgram :=
          ImpIntro.apply2(
            ProofExpr(env),
            ProofAbs("env", Ind, 
              AndElimRight.apply1(AndElimLeft.apply1(ProofVar("env")))));
        var r :- ExecuteProof(proofProgram, EnvNil);
        return checkGoal(r);
      }
    }
    // Lookup in the environment
    var envSearch := env;
    var i: nat := 0;
    while envSearch.And? && envSearch.left != goal
      decreases envSearch
    {
      envSearch := envSearch.right;
      i := i + 1;
      
    }
    if envSearch.And? && envSearch.left == goal {
      var proofElem := ProofVar("env");
      while i != 0
        decreases i
      {
        proofElem := ProofApp(ProofAxiom(AndElimRight), proofElem);
        i := i - 1;
      }
      var proofProgram := ImpIntro.apply2(
            ProofExpr(env),
            ProofAbs("env", Ind, 
              ProofApp(ProofAxiom(AndElimLeft), proofElem)));
      var r :- ExecuteProof(proofProgram, EnvNil);
      return checkGoal(r);
    }

    // Part 2: Advanced proof search (axioms with lookup in the environment)

    return Failure("Could not find a simple proof of " +  expr.ToString() );
  }

  // TODO: Transform this to a theorem that says a && b ==> b && a
  // Because we can't build proofs normally
  method {:test} TestAlcorEngine() {
    // Proof program that build A && B ==> B && A
    var proof := 
      ImpIntro.apply2(
        ProofExpr(And(Var("a"), Var("b"))),
        ProofAbs("h0", Ind, 
          Let("hA", Ind, AndElimLeft.apply1(ProofVar("h0")),
          Let("hB", Ind, AndElimRight.apply1(ProofVar("h0")),
            AndIntro.apply2(ProofVar("hB"), ProofVar("hA")))
          )));
    var result :- expect CheckProof(proof, EnvNil,
      Imp(And(Var("a"), Var("b")), And(Var("b"), Var("a"))));
  }

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
  }
}