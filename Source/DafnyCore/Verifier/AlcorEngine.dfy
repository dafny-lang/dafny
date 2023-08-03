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
         provides Proof.ForallIntro, Proof.ForallElim
         provides Wrappers, Expr.ToString
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

  // An environment makes it possible to interpret a proof program with free variables

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

  // Should be the main API if a user writes a proof explicitly
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

  opaque function checkGoalAgainstExpr(pv: ProofValue, expr: Expr, pr: ProofProgram)
    : (result: Result<(Proof, ProofProgram)>)
    requires ExecuteProof(pr, EnvNil) == Success(pv)
    ensures result.Success? ==>
      && result.value.0.GetExpr() == expr
      && pv.OneProof? && pv.proof == result.value.0
      && Success(OneProof(result.value.0)) == ExecuteProof(result.value.1, EnvNil)
  {
    if !pv.OneProof? then Failure("DummyProofFinder did not generate a proof but " + pv.Summary()) else
      var p := pv.proof;
      if p.GetExpr() == expr then Success((p, pr)) else
      Failure("DummyProofFinder was looking for a proof of " + expr.ToString() + " but returned a proof of " + p.GetExpr().ToString())
  }

  //////////////// Axiom finders //////////////////

  const CantApplyAndProofFinder := Failure("Can't apply AndElim proof finder")

  method AndProofFinder(expr: Expr)
    returns (result: Result<(Proof, ProofProgram)>)
    requires expr.Imp?
    ensures result.Success? ==>
      && result.value.0.GetExpr() == expr
      && Success(OneProof(result.value.0)) == ExecuteProof(result.value.1, EnvNil) // TODO Execute works
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
        var r :- ExecuteProof(proofProgram, EnvNil);
        result := checkGoalAgainstExpr(r, expr, proofProgram);
        return;
      }
      if A0.right == goal {
        var proofProgram :=
          ImpIntro.apply2(
            ProofExpr(env),
            ProofAbs("env", Ind, 
              AndElimRight.apply1(AndElimLeft.apply1(ProofVar("env")))));
        var r :- ExecuteProof(proofProgram, EnvNil);
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
        var r :- ExecuteProof(proofProgram, EnvNil);
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
        var r :- ExecuteProof(proofProgram, EnvNil);
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
      && Success(OneProof(result.value.0)) == ExecuteProof(result.value.1, EnvNil) // TODO Execute works
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
      var r :- ExecuteProof(proofProgram, EnvNil);
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
      && Success(OneProof(result.value.0)) == ExecuteProof(result.value.1, EnvNil) // TODO Execute works
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
      var r :- ExecuteProof(proofProgram, EnvNil);
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
      var r :- ExecuteProof(proofProgram, EnvNil);
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
      && Success(OneProof(result.value.0)) == ExecuteProof(result.value.1, EnvNil) // TODO Execute works
  {
    var checkGoal: (ProofValue, ProofProgram) --> Result<(Proof, ProofProgram)> := 
      (pv: ProofValue, pr: ProofProgram) 
        requires ExecuteProof(pr, EnvNil) == Success(pv)
      => checkGoalAgainstExpr(pv, expr, pr);
    // Given an expression (A0 && (A1 && (A2 && .... True))) ==> G
    // Will try to find a proof of it.
    // * If A1 is (a && b) and G is b, we emit the proof
    // * If A1 is a and A0 is b and G is a && b, we emit the proof
    // * If A1 is (a ==> b) and A0 is a and G is b, we emit the proof.
    if !expr.Imp? {
      result := Failure("Alcor requires an implication");
      assert result.Success? ==>
        Success(OneProof(result.value.0)) == ExecuteProof(result.value.1, EnvNil);
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
        var execEnv := EnvCons("a_x_imp_b", OneProof(proofOfConclusion.value.0), EnvNil);
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
        assert ExecuteProof(proofProgram, EnvNil) == Success(r); // No need to recompute!
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