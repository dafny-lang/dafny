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

abstract module AlcorKernelInterface {
  type Proof(!new,==)
}

module AlcorProofKernel refines AlcorKernelInterface {
  import opened Wrappers
    // We provide ways for external users to create exprs and a proof.
    // Alcor can run the proof to see if it obtains an expe
  export provides Proof, Proof.GetExpr
    provides Proof.AndIntro, Proof.AndElimLeft, Proof.AndElimRight
    provides Proof.ImpElim, Proof.ImpIntro
    provides Proof.ForallIntro, Proof.ForallElim
    provides Wrappers, Expr.ToString, NewNotInFreeVars, MaxVersion
    provides Identifier.ToString
    provides Expr.Bind, Expr.FreeVars, Expr.size
    provides AllProofs, IsInAllProofs // TODO: No longer necessary when possible to export that Proof is not a reference type
    reveals Expr, Expr.Not
    reveals Identifier

  datatype Identifier = Identifier(name: string, version: nat := 0, lbl: string := "")
  {
    function ToString(): string {
      name
      + (if lbl != "" then "@" + lbl else "")
      + (if version == 0 then "" else "@" + IntToString(version))
    }
  }

  ghost function MaxVersion(vars: set<Identifier>): (version: nat)
    ensures forall id <- vars :: id.version <= version
  {
    if |vars| == 0 then 0
    else
      var id :| id in vars;
      var m := MaxVersion(vars - {id});
      if m > id.version then m else id.version
  }
  opaque function NewNotInFreeVars(id: Identifier, freeVars: set<Identifier>): (r: Identifier)
    ensures r !in freeVars && r.name == id.name && r.lbl == id.lbl
    decreases if id in freeVars then MaxVersion(freeVars) + 1 - id.version else 0
  {
    if id in freeVars then
      NewNotInFreeVars(Identifier(id.name, id.version + 1, id.lbl), freeVars)
    else
      id
  }

  // TODO: Intermediate language for Dafny, including references, sets, etc.
  datatype Expr =
    | True
    | False
    | And(left: Expr, right: Expr)
    | Imp(left: Expr, right: Expr)
    | Eq(left: Expr, right: Expr) // Same as Iff but for everything
    | Or(left: Expr, right: Expr)
    | Var(id: Identifier)
    | Abs(id: Identifier, body: Expr)
    | App(left: Expr, right: Expr)
    | Forall(body: Expr) // Typically an Abs, but can be a name
  {
    static function Not(expr: Expr): Expr {
      Imp(expr, False)
    }
    function FreeVars(): set<Identifier> {
      if True? || False? then {} else
      if And? || Imp? || Eq? || Or? || App? then
        left.FreeVars() + right.FreeVars()
      else if Var? then
        {id}
      else if Abs? then
        body.FreeVars() - {id}
      else if Forall? then
        body.FreeVars()
      else assert false; match () {}
    }
    ghost function size(): nat {
      match this
      case True | False => 1
      case And(left, right) => left.size() + right.size() + 1
      case Imp(left, right) => left.size() + right.size() + 1
      case Eq(left, right) => left.size() + right.size() + 1
      case Or(left, right) => left.size() + right.size() + 1
      case App(left, right) => left.size() + right.size() + 1
      case Var(i) =>  1
      case Abs(i, body) => body.size() + 1
      case Forall(body) => body.size() + 1
    }
    // Ensures free variables in expr are not captured while binding.
    function Bind(id: Identifier, expr: Expr, freeVars: set<Identifier> := expr.FreeVars()): (r: Expr)
      requires freeVars == expr.FreeVars()
      ensures expr.Var? ==> r.size() == this.size()
      decreases size(), if Abs? && this.id in freeVars then 1 else 0
    {
      match this
      case True | False => this
      case And(left, right) => And(left.Bind(id, expr), right.Bind(id, expr))
      case Imp(left, right) => Imp(left.Bind(id, expr), right.Bind(id, expr))
      case Eq(left, right) => Eq(left.Bind(id, expr), right.Bind(id, expr))
      case Or(left, right) => Or(left.Bind(id, expr), right.Bind(id, expr))
      case Var(i) =>
        if i == id then expr else this
      case Abs(i, body) =>
        if i == id then this else
        if i in freeVars then // Need to rename n to avoid capture.
          var i' := NewNotInFreeVars(i, freeVars);
          var newAbs := Abs(i', body.Bind(i, Var(i')));
          newAbs.Bind(id, expr, freeVars)
        else
          Abs(i, body.Bind(id, expr, freeVars))
      case App(left, right) => App(left.Bind(id, expr), right.Bind(id, expr))
      case Forall(body) => Forall(body.Bind(id, expr))
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
        id.ToString()
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
        "\\" + id.ToString() + "." + body.ToStringWrap(p + 1)
      else if App? then
        left.ToStringWrap(p) + " " + right.ToStringWrap(p)
      else if Forall? then
        if body.Abs? then
          "forall " + body.id.ToString() + " :: " + body.body.ToStringWrap(p + 1)
        else
          "forall " + body.ToStringWrap(p + 1)
      else
        Operator()
    }
  }
  ghost const {:axiom} AllProofs: iset<Proof>
  lemma {:axiom} IsInAllProofs(p: Proof)
    ensures p in AllProofs

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
    // But one problem with our current approach is that we can't reason about what ImpIntro provides as a result.
    static function ImpIntro(hypothesis: Expr, pHypothesis: Proof -> Result<Proof>): (r: Result<Proof>)
      ensures
        forall p: Proof <- AllProofs |
               p.GetExpr() == hypothesis && pHypothesis(p).Success? ::
          r.Success? && r.value.GetExpr() == Imp(hypothesis, pHypothesis(p).value.GetExpr())
    {
      var p := Proof(hypothesis);
      IsInAllProofs(p);
      var result :- pHypothesis(p);
      Success(Proof(Imp(hypothesis, result.expr)))
    }

    static function ForallElim(theorem: Proof, instance: Expr): Result<Proof> {
      if !theorem.expr.Forall? then
        Failure("To apply ForallElim, you need to pass a proven forall expression as the first parameter, but got a proof " + theorem.expr.ToString())
      else if !theorem.expr.body.Abs? then
        Failure("To apply ForallElim, the forall must be over a lambda, but got " + theorem.expr.body.ToString())
      else
        Success(Proof(theorem.expr.body.body.Bind(theorem.expr.body.id, instance)))
    }

    static function ForallIntro(theorem: Proof, id: Identifier): Result<Proof> {
      Success(Proof(Forall(Abs(id, theorem.expr))))
    }
  }
}

// Rename in AlcorProceduralProofChecker
module Alcor {
  import opened Wrappers
  import opened AlcorProofKernel

  //  a proof program is a program in SLTC + axioms + inline expressions
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
      case ProofApp(ProofAbs(varName, tpe, body), varContent) =>
        "var " + varName + ": " + tpe.ToString() + " := " + varContent.ToString() + ";\n" +
        body.ToString()
      case ProofAbs(name, tpe, body) => "(\\"+name+". "+body.ToString()+")"
      case ProofApp(left, right) => left.ToString() + "(" + right.ToString() + ")"
      case ProofAxiom(axiom) => axiom.ToString()
      case ProofExpr(expr) => "``" + expr.ToString() + "``"
    }
  }

  function Let(name: string, tpe: Type, expression: ProofProgram, body: ProofProgram): ProofProgram {
    ProofApp(ProofAbs(name, tpe, body), expression)
  }

  // Programs above can evaluate to any proof values

  datatype ProofValue =
    | OneProof(proof: Proof)
    | OneExpr(expr: Expr)
    | OneClosure(argName: string, tpe: Type, body: ProofProgram, environment: ProofEnv)
    | OneClosureAxiom(args: seq<ProofValue>, axiom: ProofAxiom)
  {
    function Summary(): string {
      if OneProof? then "proof"
      else if OneClosure? then "proof closure" // TODO of typo
      else if OneExpr? then "expr"
      else "incomplete axiom instantiation"
    }
  }

  // An environment makes it possible to interpret a proof program with free variables

  datatype ProofEnv =
    | ProofEnvNil
    | ProofEnvCons(name: string, value: ProofValue, tail: ProofEnv)
  {
    function Lookup(searchName: string): Result<ProofValue> {
      if ProofEnvNil? then Failure("Did not find "+searchName+" in the proof environment")
      else if name == searchName then
        Success(value)
      else
        tail.Lookup(searchName)
    }
  }

  // Proof axiom values

  datatype ProofAxiom =
    | AndIntro
    | AndElimLeft
    | AndElimRight
    | ImpElim
    | ImpIntro
    | ForallElim
    | ForallIntro
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
      case ForallIntro => "ForallIntro"
      case ForallElim => "ForallElim"
    }
    function Arity(): nat {
      match this {
        case AndIntro => 2
        case AndElimLeft => 1
        case AndElimRight => 1
        case ImpIntro => 2
        case ImpElim => 2
        case ForallIntro => 2
        case ForallElim => 2
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
    function {:fuel 30, 30} ApplyArgs(ghost program: ProofProgram, args: seq<ProofValue>, environment: ProofEnv): Result<ProofValue>
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
                                                          var x :- ExecuteProof(body, ProofEnvCons(argName, OneProof(p), environment));
                                                          if x.OneProof? then Success(x.proof)
                                                          else Failure("Closure should return a proof, but got " + x.Summary());
            Proof.ImpIntro(hypothesis, proofBuilder).Map(p => OneProof(p))
        case ImpElim =>
          var left :- ExtractProof(args, 0);
          var right :- ExtractProof(args, 1);
          Proof.ImpElim(left, right).Map(p => OneProof(p))
        case ForallIntro =>
          var v :- ExtractExpr(args, 0);
          if !v.Var? then
            Failure("ForallIntro needs a var as first argument, but got " + v.ToString())
          else
            var body :- ExtractProof(args, 1);
            Proof.ForallIntro(body, v.id).Map(p => OneProof(p))
        case ForallElim =>
          var axiom :- ExtractProof(args, 0);
          var instance :- ExtractExpr(args, 1);
          Proof.ForallElim(axiom, instance).Map(p => OneProof(p))
      }
    }
  }


  // TODO: Type system
  datatype Type = Ind | Bool | Arrow(left: Type, right: Type) {
    function ToString(): string {
      if Ind? then "Ind" else
      if Bool? then "Bool" else
      assert Arrow?;
      (if left.Arrow? then "(" + left.ToString() + ")" else left.ToString())
      + "->" + right.ToString()
    }
  }

  // TODO: Replace decreases step by a fuel or prove termination
  ghost function {:axiom} DecreasesStep(program: ProofProgram): nat

  function Debug(msg: string): (result: int) {
    0
  } by method {
    print msg;
    result := 0;
  }

  // A call-by-value proof program should be guaranteed to terminate by construction
  opaque function ExecuteProof(program: ProofProgram, environment: ProofEnv): Result<ProofValue>
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
          ExecuteProof(result.body, ProofEnvCons(result.argName, argument, result.environment))
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

  // Should be the main API if a user writes a proof explicitly
  function CheckProof(program: ProofProgram, environment: ProofEnv, expected: Expr): Result<Proof> {
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

  opaque function checkGoalAgainstExpr(pv: ProofValue, expr: Expr, pr: ProofProgram)
    : (result: Result<(Proof, ProofProgram)>)
    requires ExecuteProof(pr, ProofEnvNil) == Success(pv)
    ensures result.Success? ==>
              && result.value.0.GetExpr() == expr
              && pv.OneProof? && pv.proof == result.value.0
              && Success(OneProof(result.value.0)) == ExecuteProof(result.value.1, ProofEnvNil)
  {
    if !pv.OneProof? then Failure("DummyProofFinder did not generate a proof but " + pv.Summary()) else
    var p := pv.proof;
    if p.GetExpr() == expr then Success((p, pr)) else
    Failure("DummyProofFinder was looking for a proof of " + expr.ToString() + " but returned a proof of " + p.GetExpr().ToString())
  }

  //////////////// Given a proofprogram that A ==> B and B ==> C, builds a proof program that A ==> C
  method Combine(a: Expr, aToB: ProofProgram, bToC: ProofProgram)
    returns (aToC: ProofProgram)
    requires
      var pAB := ExecuteProof(aToB, ProofEnvNil);
      var pBC := ExecuteProof(bToC, ProofEnvNil);
      && pAB.Success? && pBC.Success?
      && pAB.value.OneProof? && pBC.value.OneProof?
      && pAB.value.proof.GetExpr().Imp?
      && pAB.value.proof.GetExpr().left == a
      && pBC.value.proof.GetExpr().Imp?
      && pAB.value.proof.GetExpr().right == pBC.value.proof.GetExpr().left
    ensures
      var pAB := ExecuteProof(aToB, ProofEnvNil);
      var pBC := ExecuteProof(bToC, ProofEnvNil);
      var pAC := ExecuteProof(aToC, ProofEnvNil);
      && pAC.Success?
      && pAC.value.OneProof? && pAC.value.proof.GetExpr().Imp?
      && pAC.value.proof.GetExpr().left == pAB.value.proof.GetExpr().left
      && pAC.value.proof.GetExpr().right == pBC.value.proof.GetExpr().right
  {
    ghost var pAB := ExecuteProof(aToB, ProofEnvNil);
    ghost var pBC := ExecuteProof(bToC, ProofEnvNil);
    assert pAB.Success? && pBC.Success?;
    assert pAB.value.OneProof? && pBC.value.OneProof?;
    aToC :=
      Let("aToB", Ind, aToB,
      Let("bToC", Ind, bToC,
        ImpIntro.apply2(ProofExpr(a),
          ProofAbs("a", Ind,
            Let("B", Ind, ImpElim.apply2(ProofVar("aToB"), ProofVar("a")),
              Let("C", Ind, ImpElim.apply2(ProofVar("bToC"), ProofVar("B")),
              ProofVar("C")
            )
          )
        )
      )
      ));
    // TODO: Prove the postcondition
    assert false;
  }


  //////////////// Axiom finders //////////////////

  const CantApplyAndProofFinder := Failure("Can't apply AndElim proof finder")

  method AndProofFinder(expr: Expr)
    returns (result: Result<(Proof, ProofProgram)>)
    requires expr.Imp?
    ensures result.Success? ==>
              && result.value.0.GetExpr() == expr
              && Success(OneProof(result.value.0)) == ExecuteProof(result.value.1, ProofEnvNil) // TODO Execute works
  {
    if !expr.left.And? {
      return CantApplyAndProofFinder;
    }
    var goal := expr.right;
    var env := expr.left;
    var A0 := env.left;
    var tail := env.right;
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
        var r :- ExecuteProof(proofProgram, ProofEnvNil);
        result := checkGoalAgainstExpr(r, expr, proofProgram);
        return;
      }
      if A0.right == goal {
        var proofProgram :=
          ImpIntro.apply2(
            ProofExpr(env),
            ProofAbs("env", Ind,
                     AndElimRight.apply1(AndElimLeft.apply1(ProofVar("env")))));
        var r :- ExecuteProof(proofProgram, ProofEnvNil);
        result := checkGoalAgainstExpr(r, expr, proofProgram);
        return;
      }
    }
    if tail.And? {
      var A1 := tail.left;
      if goal == And(A0, A1) {
        var proofProgram :=
          ImpIntro.apply2(
            ProofExpr(env),
            ProofAbs("env", Ind,
                     AndIntro.apply2(AndElimLeft.apply1(ProofVar("env")),
                                     AndElimLeft.apply1(AndElimRight.apply1(ProofVar("env"))))
            )
          );
        var r :- ExecuteProof(proofProgram, ProofEnvNil);
        result := checkGoalAgainstExpr(r, expr, proofProgram);
        return;
      }
      if goal == And(A1, A0) {
        var proofProgram :=
          ImpIntro.apply2(
            ProofExpr(env),
            ProofAbs("env", Ind,
                     AndIntro.apply2(AndElimLeft.apply1(AndElimRight.apply1(ProofVar("env"))),
                                     AndElimLeft.apply1(ProofVar("env")))
            )
          );
        var r :- ExecuteProof(proofProgram, ProofEnvNil);
        result := checkGoalAgainstExpr(r, expr, proofProgram);
        return;
      }
    }
    return CantApplyAndProofFinder;
  }

  method LookupProofFinder(expr: Expr)
    returns (result: Result<(Proof, ProofProgram)>)
    requires expr.Imp?
    ensures result.Success? ==>
              && result.value.0.GetExpr() == expr
              && Success(OneProof(result.value.0)) == ExecuteProof(result.value.1, ProofEnvNil) // TODO Execute works
  {
    var goal := expr.right;
    var env := expr.left;
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
      var r :- ExecuteProof(proofProgram, ProofEnvNil);
      result := checkGoalAgainstExpr(r, expr, proofProgram);
      return;
    }
    return Failure("Could not apply LookupProofFinder");
  }

  const CantApplyModusPonensFinder := Failure("Can't apply ModusPonensFinder")

  method ModusPonensFinder(expr: Expr)
    returns (result: Result<(Proof, ProofProgram)>)
    requires expr.Imp?
    ensures result.Success? ==>
              && result.value.0.GetExpr() == expr
              && Success(OneProof(result.value.0)) == ExecuteProof(result.value.1, ProofEnvNil) // TODO Execute works
  {
    var goal := expr.right;
    var env := expr.left;
    if !env.And? {
      return CantApplyModusPonensFinder;
    }
    var A0 := env.left;
    var tail := env.right;
    if !tail.And? {
      return CantApplyModusPonensFinder;
    }
    var A1 := tail.left; // TODO: Do a lookup of the hypothesis
    if A0.Imp? && A0.right == goal && A1 == A0.left {
      // ((A ==> B) && (A && ...)) ==> B
      // We emit a suitable proof of the above
      var proofProgram :=
        ImpIntro.apply2(
          ProofExpr(env),
          ProofAbs("env", Ind,
                   Let("AtoB", Ind, AndElimLeft.apply1(ProofVar("env")),
                       Let("A", Ind, AndElimLeft.apply1(AndElimRight.apply1(ProofVar("env"))),
                           ImpElim.apply2(ProofVar("AtoB"), ProofVar("A"))))
          ));
      var r :- ExecuteProof(proofProgram, ProofEnvNil);
      result := checkGoalAgainstExpr(r, expr, proofProgram);
      return;
    }
    if A1.Imp? && A1.right == goal && A0 == A1.left {
      // (A && ((A ==> B) && ...)) ==> B
      // We emit a suitable proof of the above
      var proofProgram :=
        ImpIntro.apply2(
          ProofExpr(env),
          ProofAbs("env", Ind,
                   Let("A", Ind, AndElimLeft.apply1(ProofVar("env")),
                       Let("AtoB", Ind, AndElimLeft.apply1(AndElimRight.apply1(ProofVar("env"))),
                           ImpElim.apply2(ProofVar("AtoB"), ProofVar("A"))))
          ));
      var r :- ExecuteProof(proofProgram, ProofEnvNil);
      result := checkGoalAgainstExpr(r, expr, proofProgram);
      return;
    }
    return CantApplyModusPonensFinder;
  }

  // No need to trust this proof finder, if it finds a proof it's a correct one!
  method DummyProofFinder(expr: Expr)
    returns (result: Result<(Proof, ProofProgram)>)
    decreases if expr.Imp? then numberOfImp(expr.right) else 0
    ensures result.Success? ==>
              && result.value.0.GetExpr() == expr
              && Success(OneProof(result.value.0)) == ExecuteProof(result.value.1, ProofEnvNil) // TODO Execute works
  {
    var checkGoal: (ProofValue, ProofProgram) --> Result<(Proof, ProofProgram)> :=
      (pv: ProofValue, pr: ProofProgram)
      requires ExecuteProof(pr, ProofEnvNil) == Success(pv)
      => checkGoalAgainstExpr(pv, expr, pr);
    // Given an expression (A0 && (A1 && (A2 && .... True))) ==> G
    // Will try to find a proof of it.
    // * If A1 is (a && b) and G is b, we emit the proof
    // * If A1 is a and A0 is b and G is a && b, we emit the proof
    // * If A1 is (a ==> b) and A0 is a and G is b, we emit the proof.
    if !expr.Imp? {
      result := Failure("Alcor requires an implication");
      assert result.Success? ==>
          Success(OneProof(result.value.0)) == ExecuteProof(result.value.1, ProofEnvNil);
      return;
    }
    var goal := expr.right;
    var env := expr.left;
    if goal.Imp? {
      // Let's put the hypothesis in the environment and prove it.
      var proofOfConclusion := DummyProofFinder(Imp(And(goal.left, env), goal.right));
      if proofOfConclusion.Success? {
        // We have a proof that A && env ==> B
        // Now let's transform it in a proof of env ==> (A ==> B)
        var execEnv := ProofEnvCons("a_x_imp_b", OneProof(proofOfConclusion.value.0), ProofEnvNil);
        var proofProgramInner := ImpIntro.apply2(
          ProofExpr(env),
          ProofAbs("env", Ind,
                   ImpIntro.apply2(
                     ProofExpr(goal.left),
                     ProofAbs("proofOfA", Ind,
                              ImpElim.apply2(
                                ProofVar("a_x_imp_b"),
                                AndIntro.apply2(
                                  ProofVar("proofOfA"),
                                  ProofVar("env")))))));
        var r :- ExecuteProof(
          proofProgramInner, execEnv);
        var proofProgram :=
          Let("a_x_imp_b", Bool, proofOfConclusion.value.1,
              proofProgramInner
          );
        assert ExecuteProof(proofProgram, ProofEnvNil) == Success(r) by {
          reveal ExecuteProof();
        } // No need to recompute!
        result := checkGoal(r, proofProgram);
        return;
      }
    }
    // * if A0 is (a && b) and G is a, we emit the proof
    result := AndProofFinder(expr);
    if result.Success? {
      return;
    }
    result := ModusPonensFinder(expr);
    if result.Success? {
      return;
    }
    result := LookupProofFinder(expr);
    if result.Success? {
      return;
    }

    result := Failure("Could not find a simple proof of " +  expr.ToString() );
    return;
  }
}

module AlcorTacticProofChecker {
  import opened AlcorProofKernel
  import opened Alcor
  import opened Wrappers

  datatype Env = EnvNil | EnvCons(id: Identifier, prop: Expr, tail: Env) {
    function {:fuel 4, 4} ToExpr(): Expr {
      if EnvNil? then True else
      And(prop, tail.ToExpr())
    }
    predicate IsEmpty() { EnvNil? }

    ghost function Length(): nat { if EnvNil? then 0 else 1 + tail.Length() }
    function ElemAt(index: nat): (result: (Identifier, Expr))
      requires index < Length()
      ensures Drop(index).EnvCons?
      ensures result == (Drop(index).id, Drop(index).prop)
    {
      if index == 0 then (id, prop) else tail.ElemAt(index - 1)
    }

    function IndexOf(name: Identifier): (index: int)
      ensures if index >= 0 then
                && index < Length()
                && ElemAt(index).0 == name else index == -1
    {
      if this.EnvNil? then -1 else
      if this.id == name then 0 else
      var tailIndex := tail.IndexOf(name);
      if tailIndex == -1 then -1 else 1 + tailIndex
    }

    function Drop(i: nat): (result: Env)
      requires i <= Length()
      ensures result.Length() == Length() - i
    {
      if i == 0 then this else tail.Drop(i-1)
    }
    lemma DropDrop(i: nat, j: nat)
      requires i + j <= Length()
      ensures Drop(i).Drop(j) == Drop(i+j)
    {
    }

    function ReplaceTailAt(i: nat, newTail: Env --> Env): Env
      requires i <= Length()
      requires newTail.requires(Drop(i))
    {
      if i == 0 then newTail(this) else
      EnvCons(id, prop, tail.ReplaceTailAt(i-1, newTail))
    }

    function ToString(): string
    {
      if this.EnvNil? then "" else
      var x := id.ToString() + ": " + prop.ToString();
      if !tail.EnvNil? then
        tail.ToString() + "\n" + x
      else
        x
    }

    function FreeVars(): set<Identifier>
    {
      if EnvNil? then {} else
      var tailFreeVars := tail.FreeVars();
      {id} + tailFreeVars
    }

    function Rename(oldName: Identifier, newName: Identifier): Env {
      if EnvNil? then this
      else if id == oldName then EnvCons(newName, prop, tail)
      else EnvCons(id, prop, tail.Rename(oldName, newName))
    }
  }

  datatype Sequent =
    Sequent(env: Env, goal: Expr)
  {
    // Converts this sequent into a proposition
    function {:fuel 4, 4} ToExpr(envIndex: nat := 0): Expr
    {
      Imp(env.ToExpr(), goal)
    }
    function ToString(): string {
      env.ToString() + "\n|- " + goal.ToString()
    }
  }

  datatype SequentList = SequentNil | SequentCons(head: Sequent, tail: SequentList) {
    ghost function Length(): nat { if SequentNil? then 0 else 1 + tail.Length() }
    predicate IsEmpty() { SequentNil? }

    function {:fuel 4, 4} ElemAt(index: nat): Sequent
      requires index < Length()
    {
      if index == 0 then head else tail.ElemAt(index - 1)
    }
    function {:fuel 4, 4} ToExpr(): Expr {
      if SequentNil? then True else
      And(head.ToExpr(), tail.ToExpr())
    }
    function ToString(): string
    {
      if SequentNil? then ""
      else
        head.ToString() + (if tail.SequentNil? then "" else "\n\n")
        + tail.ToString()
    }
  }

  datatype ProofState = Sequents(sequents: SequentList) | Error(message: string)
  {
    function {:fuel 4, 4} ToExpr(): Expr
    {
      if Error? then False else sequents.ToExpr()
    }
    function ToString(): string
    {
      if Error? then message else sequents.ToString()
    }
    function ToError(msg: string): ProofState {
      Error("\n" + ToString() + "\n/!\\" + msg)
    }
  }

  predicate IsProof(p: Proof) { true }

  lemma ExecuteHelperAxiom(axiom: ProofAxiom)
    ensures ExecuteProof(ProofAxiom(axiom), ProofEnvNil) == Success(OneClosureAxiom([], axiom))
  {
    reveal ExecuteProof();
  }
  lemma ExecuteHelperExpr(expr: Expr)
    ensures ExecuteProof(ProofExpr(expr), ProofEnvNil) == Success(OneExpr(expr))
  {
    reveal ExecuteProof();
  }

  lemma ExecuteHelperClosure(name: string, tpe: Type, body: ProofProgram, penv: ProofEnv)
    ensures ExecuteProof(ProofAbs(name, tpe, body), penv) == Success(OneClosure(name, tpe, body, penv))
  {
    reveal ExecuteProof();
  }

  lemma ExecuteHelperAxiomApp1(app1: ProofProgram, app2: ProofProgram, app2v: ProofValue, penv: ProofEnv, args: seq<ProofValue>, axiom: ProofAxiom)
    requires ExecuteProof(app1, penv) == Success(OneClosureAxiom(args, axiom))
    requires ExecuteProof(app2, penv) == Success(app2v)
    requires |args| + 1 < axiom.Arity()
    ensures ExecuteProof(ProofApp(app1, app2), penv) == Success(OneClosureAxiom(args + [app2v], axiom))
  {
    reveal ExecuteProof();
  }

  /*    ensures
        axiom == ImpIntro ==>
        ExecuteProof(ProofApp(app1, app2), penv) ==
          Success(OneProof(), axiom))
    {
      reveal ExecuteProof();
    }*/

  class TacticMode {
    const env: Env
    const goal: Expr
    var proofState: ProofState
    var proofBuilder: ProofProgram // Builds a proof that proofState.ToExpr() ==> Imp(env.ToExpr(), goal)

    constructor (goal: Expr, env: Env)
      ensures Invariant()
    {
      this.env := env;
      this.goal := goal;
      this.proofState := Sequents(SequentCons(Sequent(env, goal), SequentNil));
      var overallGoal := And(Imp(env.ToExpr(), goal), True);
      this.proofBuilder :=
        ImpIntro.apply2(ProofExpr(overallGoal),
                        ProofAbs("goal", Ind, ProofVar("goal")));
      new;
      assert proofState.ToExpr() == And(Imp(env.ToExpr(), goal), True);
      CheckProof();
    }
    // Call this method to fail internal errors early
    method CheckProof()
      modifies this
      ensures Invariant()
    {
      var overallGoal := And(Imp(env.ToExpr(), goal), True);
      var p := ExecuteProof(proofBuilder, ProofEnvNil);
      if p.Failure? {
        proofState := Error("[Internal error] " + p.msg);
      } else if !p.value.OneProof? {
        proofState := Error("[Internal error] Expected a proof, got a " + p.value.Summary());
      } else if p.value.proof.GetExpr() != Imp(proofState.ToExpr(), overallGoal) {
        proofState := Error("[Internal error] Expected a proof that the proof state implies the overall goal\n" +
          Imp(proofState.ToExpr(), overallGoal).ToString() + "\n" +
          ", got a proof of\n" +
          p.value.proof.GetExpr().ToString());
      } else {
        assert p.value.OneProof? && p.value.proof.GetExpr() ==
                                    Imp(proofState.ToExpr(), overallGoal);
      }
    }
    ghost predicate Invariant()
      reads this
    {
      proofState.Sequents? ==>
        && var p := ExecuteProof(proofBuilder, ProofEnvNil);
        && p.Success? && p.value.OneProof? && p.value.proof.GetExpr() ==
                                              Imp(proofState.ToExpr(), And(Imp(env.ToExpr(), goal), True))
    }

    method Finish() returns (result: Result<(Proof, ProofProgram)>)
      ensures result.Success? ==> result.value.0.GetExpr() == Imp(env.ToExpr(), goal)
    {
      return Failure("TODO");
    }

    ghost predicate HasProof() reads this`proofState {
      && proofState.Sequents?
      && exists p: Proof <- AllProofs :: p.GetExpr() == proofState.ToExpr()
    }

    // Works for implications and foralls
    method {:only} Intro(name: string := "h") returns (feedback: Result<string>)
      //requires Invariant()
      modifies this
      //ensures proofState.ToExpr()
      //ensures Invariant()
      ensures HasProof() ==> old(HasProof())
    {
      if proofState.Error? {
        return Failure(proofState.message);
      }
      var sequents := proofState.sequents;
      if sequents.SequentNil? {
        return Failure("Nothing to introduce, proof state is empty. Consider removing this");
      }
      var sequent := sequents.head;
      var id := Identifier(name);
      if sequent.goal.Forall? && sequent.goal.body.Abs? {
        // We make sure we create a new identifier, automatic or provided
        var freeVariables := sequent.env.FreeVars();
        var freeVar := NewNotInFreeVars(sequent.goal.body.id, freeVariables);
        proofState := Sequents(
          sequents.(head :=
          sequent.(goal :=
          sequent.goal.body.body.Bind(sequent.goal.body.id, Var(freeVar))
          )
          )
        );
        assert HasProof() ==> old(HasProof());
      } else if sequent.goal.Imp? {
        // Here we simply put the left in the environment;
        proofState := Sequents(
          sequents.(head :=
          Sequent(env := EnvCons(id, sequent.goal.left, sequent.env),
                  goal := sequent.goal.right)
          )
        );
        assert {:only} HasProof() ==> old(HasProof()) by {
          ghost var ps := proofState;
          if HasProof() {
            var p :| p in AllProofs && p.GetExpr() == ps.ToExpr();
            var others := ps.sequents.tail.ToExpr();
            var B := ps.sequents.head.goal;
            var A := ps.sequents.head.env.ToExpr().left;
            var Env := ps.sequents.head.env.ToExpr().right;
            assert ps.ToExpr() == And(Imp(And(A, Env), B), others);
            assert old(proofState).ToExpr() == And(Imp(Env, Imp(A, B)), others);
            // Before: (Env ==> (A ==> B)) && Others
            // Now: (A && Env ==> B) && Others
            var p2 : Proof;
            assert p2 in AllProofs && p2.GetExpr() == old(proofState.ToExpr());
            assert old(HasProof());
          }
        }
      } else {
        proofState := Error("Could not apply intro rule");
      }
      if proofState.Error? {
        feedback := Failure(proofState.message);
      } else {
        feedback := Success(proofState.ToString());
      }
      //CheckProof();
    }

    // TODO: Putting a default value for suggestedName like Identifier("") crashes Dafny
    method Rename(previousName: Identifier, suggestedName: Identifier) returns (feedback: Result<string>)
      modifies this
    {
      var oldName := previousName;
      var newName := suggestedName;
      if proofState.Error? {
        return Failure(proofState.message);
      }
      var sequents := proofState.sequents;
      if sequents.SequentNil? {
        return Failure("Nothing to rename, proof state is empty. Consider removing this");
      }
      var sequent := sequents.head;
      var env := sequent.env;
      if env.EnvNil? {
        return Failure("Nothing to rename, proof state has no environment. Consider removing this");
      }
      if newName == Identifier("") { // Last thing to rename
        newName := oldName;
        oldName := env.id;
      }
      if oldName !in env.FreeVars() {
        return Failure("No variable in the environment is named " + oldName.ToString());
      }
      var newEnv := env.Rename(oldName, newName);
      proofState := proofState.(
      sequents := sequents.(
      head := Sequent(newEnv, sequent.goal)
      )
      );
      return Success(proofState.ToString());
    }

    method Cases() returns (feedback: Result<string>)
      modifies this
    {
      if proofState.Error? {
        return Failure(proofState.message);
      }
      var sequents := proofState.sequents;
      if sequents.SequentNil? {
        return Failure("Nothing to perform a case split on");
      }
      var sequent := sequents.head;
      if(!sequent.goal.And?) {
        return Failure("Cannot perform a case split on something other than &&");
      }
      var env := sequent.env;
      var newSequents := SequentCons(
        Sequent(env, sequent.goal.left),
        SequentCons(
        Sequent(env, Imp(sequent.goal.left, sequent.goal.right)),
        sequents.tail));
      proofState := Sequents(newSequents);
      return Success(proofState.ToString());
    }

    method CasesEnv(name: string, left: string, right: string) returns (feedback: Result<string>)
      modifies this
    {
      if proofState.Error? {
        return Failure(proofState.message);
      }

      var sequents := proofState.sequents;
      if sequents.SequentNil? {
        return Failure("Nothing to perform a case split on");
      }
      var sequent := sequents.head;
      var env := sequent.env;
      var i := env.IndexOf(Identifier(name));
      if i < 0 {
        return Failure("Entry " + name + " not found in the environment");
      }
      var (envIdentifier, envElem) := env.ElemAt(i);
      if !envElem.And? {
        return Failure("Entry " + name + " is not splittable");
      }
      var left := Identifier(left);
      var right := Identifier(right);
      var newEnv := env.ReplaceTailAt(i, (previousEnv: Env) requires previousEnv == env.Drop(i) => 
        assert previousEnv.prop.And?;
        EnvCons(right, previousEnv.prop.right,
        EnvCons(left, previousEnv.prop.left, 
        previousEnv.tail))
      );
      var newSequents := SequentCons(
        Sequent(newEnv, sequent.goal),
        sequents.tail);
      proofState := Sequents(newSequents);
      return Success(proofState.ToString());
    }

    method ImpElim(imp: string, hypothesis: string, newName: string := "") returns (feedback: Result<string>)
      modifies this
    {
      if proofState.Error? {
        return Failure(proofState.message);
      }

      var sequents := proofState.sequents;
      if sequents.SequentNil? {
        return Failure("Nothing to perform a ImpElim on");
      }
      var sequent := sequents.head;
      var env := sequent.env;
      var goal := sequent.goal;
      var iImp := env.IndexOf(Identifier(imp));
      if iImp < 0 {
        return Failure("Entry " + imp + " not found in the environment");
      }
      var iHyp := env.IndexOf(Identifier(hypothesis));
      if iHyp < 0 {
        return Failure("Entry " + hypothesis + " not found in the environment");
      }
      var (_, impExpr) := env.ElemAt(iImp);
      var (_, hypExpr) := env.ElemAt(iHyp);
      if !impExpr.Imp? {
        return Failure("Entry " + imp + " is not an implication");
      }
      if impExpr.left != hypExpr {
        return Failure("Entry " + imp + " cannot be applied to " + hypothesis);
      }
      if impExpr.right == goal {
        proofState := Sequents(
          sequents.tail
        );
      } else {
        var newName := if newName == "" then "h" else newName;
        var freeVariables := sequent.env.FreeVars();
        var freeVar := NewNotInFreeVars(Identifier(newName), freeVariables);
        proofState := Sequents(
          SequentCons(
            Sequent(EnvCons(freeVar, impExpr.right, env), goal),
            sequents.tail
          )
        );
      }
      return Success(proofState.ToString());
    }

    method UseHypothesis(name: string) returns (feedback: Result<string>)
      modifies this
    {
      if proofState.Error? {
        return Failure(proofState.message);
      }

      var sequents := proofState.sequents;
      if sequents.SequentNil? {
        return Failure("Nothing to perform a ImpElim on");
      }
      var sequent := sequents.head;
      var env := sequent.env;
      var goal := sequent.goal;
      var iHyp := env.IndexOf(Identifier(name));
      if iHyp < 0 {
        return Failure("Entry " + name + " not found in the environment");
      }
      var (_, hypExpr) := env.ElemAt(iHyp);
      if hypExpr == goal {
        proofState := Sequents(
          sequents.tail
        );
      } else {
        return Failure("The hypothesis " + name + " is not the goal");
      }
      return Success(proofState.ToString());
    }

    /*method Intro(name: string) modifies this
      ensures HasProofFor(proofState) ==> HasProofFor(old(proofState))
    {
      ghost var oldProofState := proofState;
      if proofState.Error? {
        return;
      }
      if proofState.sequents.IsEmpty() {
        proofState := proofState.ToError("Please remove Intro() because there is nothing left to prove. You're all set!");
        return;
      }
      var ps := proofState.sequents.head;
      var result := Need(ps.goal.Imp?, () => "Intro() requires an ==>, got " + ps.goal.Operator());
      if !ps.goal.Imp? {
        proofState := proofState.ToError("Intro() requires an ==>, got " + ps.goal.Operator());
      } else {
        var newSequents := SequentCons(Sequent(EnvCons(name, ps.goal.left, ps.env), ps.goal.right), proofState.sequents.tail);
        proofState := Sequents(newSequents);
        if HasProofFor(proofState) {
          var propOld := oldProofState.ToExpr();
          var propNew := proofState.ToExpr();
          var proof: Proof :| proof.prop == propNew;
          /*assert propNew ==
            And(
              Imp(
                And(
                  propOld.left.right.left, //propNew.left.left.left  // The hypothesis of the goal is here
                  propOld.left.left        //propNew.left.left.right // The previous environment is here
                ),
                propOld.left.right.right   //propNew.left.left.right, // The conclusion of the goal is here
              ),
              propOld.right                //propNew.left.right // The other sequents are here.
            );
          assert propOld ==
            And(
              Imp(
                propNew.left.left.right,  // The previous environment
                Imp(propNew.left.left.left, propNew.left.right) // The previous goal is an implication
              ),
              propNew.right
            );*/
          var pRight := AndRight(proof).value; // The proof of other sequents
          var pLeftNew := AndLeft(proof).value; // The proof of the new sequent
          var pLeft: Proof := ImpIntro_(propNew.left.left.right,
      (proofPrevEnv: Proof) requires proofPrevEnv.prop == propNew.left.left.right =>
        ImpIntro_(propNew.left.left.left,
      (proofHypothesisGoal: Proof) requires proofHypothesisGoal.prop == propNew.left.left.left =>
        var proofOfAnd := AndIntro(proofHypothesisGoal, proofPrevEnv);
        ImpElim_(pLeftNew, proofOfAnd)
        ));
          var finalProof := AndIntro(pLeft, pRight);
          assert HasProofFor(oldProofState);
        }
      }
    }
    method Cases(name: string) modifies this {
      if proofState.Error? {
        return;
      }
      if proofState.sequents.IsEmpty() {
        proofState := proofState.ToError("Cannot Cases() because nothing else to prove");
        return;
      }
      var ps := proofState.sequents.head;
      var i := ps.env.IndexOf(name);
      if i < 0 {
        proofState := proofState.ToError("Could not find " + name + " in proof state");
        return;
      }
      var binding := ps.env.ElemAt(i);
      if binding.1.And? {
        var psEnv' := ps.env.ReplaceTailAt(i, (previous: Env) requires previous == ps.env.Drop(i) =>
        EnvCons(name + ".left", binding.1.left,
                EnvCons(name + ".right", binding.1.right, previous.tail)));
        proofState := Sequents(SequentCons(Sequent(psEnv', ps.goal),proofState.sequents.tail));
      } else if binding.1.Or? {
        // We split the goal into
        var ps1 := ps.env.ReplaceTailAt(i, (previous: Env) requires previous == ps.env.Drop(i) =>
        EnvCons(name + ".left", binding.1.left, previous.tail));
        var ps2 := ps.env.ReplaceTailAt(i, (previous: Env) requires previous == ps.env.Drop(i) =>
        EnvCons(name + ".right", binding.1.right, previous.tail));
        proofState := Sequents(
          SequentCons(Sequent(ps1, ps.goal),
                      SequentCons(Sequent(ps2, ps.goal),
                                  proofState.sequents.tail
                      )));
      } else {
        proofState := proofState.ToError("Cannot split " + name + " because it's not && or || but " + binding.1.Operator());
        return;
      }
    }
    method Contradiction() modifies this {
      // O(n²) method to find contradictions if the goal is to prove false.
      if proofState.Error? {
        return;
      }
      if proofState.sequents.IsEmpty() {
        proofState := proofState.ToError("Cannot Contradiction() because nothing else to prove");
        return;
      }
      var ps := proofState.sequents.head;
      if ps.goal != False {
        proofState := proofState.ToError("Cannot Contradiction() because goal is not false");
        return;
      }
      var psEnvLength := ps.env.Length();
      if psEnvLength < 2 {
        proofState := proofState.ToError("Did not find any contradictions - Environment too small");
        return;
      }
      var i: nat := 0;
      var j: nat := 0;
      var envI := ps.env;
      ghost var proofStateInit := proofState;
      for i := 0 to psEnvLength - 1
        invariant envI == ps.env.Drop(i)
        invariant proofStateInit == proofState
      {
        var envJ := envI.tail;
        assert envI.tail == envI.Drop(1) == ps.env.Drop(i).Drop(1);
        ps.env.DropDrop(i, 1);
        for j := i + 1 to psEnvLength
          invariant envJ == ps.env.Drop(j)
          invariant proofStateInit == proofState
        {
          if envI.prop == Expr.Not(envJ.prop)
             || Expr.Not(envI.prop) == envJ.prop {
            proofState := Sequents(proofState.sequents.tail);
            return;
          }
          envJ := envJ.tail;
          ps.env.DropDrop(j, 1);
        }
        envI := envI.tail;
      }
      proofState := proofState.ToError("Did not find any contradictions");
      return;
    }*/
  }
}









