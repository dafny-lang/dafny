// RUN: %dafny /compile:0 /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This module proves the correctness of the algorithms.  It leaves a number of things undefined.
// They are defined in refinement modules below.
abstract module M0 {
  /******* State *******/
  type State
  ghost function DomSt(st: State): set<Path>
  ghost function GetSt(p: Path, st: State): Artifact
    requires p in DomSt(st);

  ghost predicate ValidState(st: State)
  {
    forall p :: p in DomSt(st) ==> WellFounded(p)
  }
  ghost predicate WellFounded(p: Path)

  // The specification given for this Union is liberal enough to allow incompatible
  // states, that is, st and st' are allowed to disagree on some paths.  Any such disagreement
  // will be resolved in favor of st.  For the purpose of supporting function Combine, we are
  // only ever interested in combining/unioning compatible states anyhow.
  ghost function Union(st: State, st': State): State
    ensures
      var result := Union(st, st');
      DomSt(result) == DomSt(st) + DomSt(st') &&
      forall p :: p in DomSt(result) ==>
        GetSt(p, result) == GetSt(p, if p in DomSt(st) then st else st');

  ghost predicate Compatible(sts: set<State>)
  {
    forall st, st', p :: st in sts && st' in sts && p in DomSt(st) && p in DomSt(st') ==>
      GetSt(p, st) == GetSt(p, st')
  }

  ghost function Combine(sts: set<State>): State
    requires sts != {};
  {
    var st :| st in sts;
    if sts == {st} then
      st
    else
      Union(st, Combine(sts - {st}))
  }
  lemma Lemma_Combine(sts: set<State>, parent: State)
    requires sts != {};
    requires forall st :: st in sts ==> ValidState(st) && Extends(parent, st);
    ensures ValidState(Combine(sts)) && Extends(parent, Combine(sts));
  {
    forall st | st in sts && (sts == {st} || Combine(sts) == Union(st, Combine(sts - {st})))
      ensures Extends(parent, Combine(sts));
    {
    }
  }

  /******* Environment *******/
  type Env
  ghost predicate ValidEnv(env: Env)
  ghost function EmptyEnv(): Env
    ensures ValidEnv(EmptyEnv());
  ghost function GetEnv(id: Identifier, env: Env): Expression
    requires ValidEnv(env);
    ensures Value(GetEnv(id, env));
  ghost function SetEnv(id: Identifier, expr: Expression, env: Env): Env
    requires ValidEnv(env) && Value(expr);
    ensures ValidEnv(SetEnv(id, expr, env));

  /******* Primitive function 'exec' *******/
  ghost function exec(cmd: string, deps: set<Path>, exps: set<string>, st: State): Tuple<set<Path>, State>

  lemma ExecProperty(cmd: string, deps: set<Path>, exps: set<string>, st: State)
    requires
      ValidState(st) &&
      deps <= DomSt(st) &&
      Pre(cmd, deps, exps, st);
    ensures
      var Pair(paths, st') := exec(cmd, deps, exps, st);
      ValidState(st') &&
      Extends(st, st') &&
      OneToOne(cmd, deps, exps, paths) &&
      Post(cmd, deps, exps, st');

  ghost predicate Pre(cmd: string, deps: set<Path>, exps: set<string>, st: State)
  {
    forall e :: e in exps ==>
      Loc(cmd, deps, e) in DomSt(st) ==> GetSt(Loc(cmd, deps, e), st) == Oracle(Loc(cmd, deps, e), st)
  }

  ghost predicate OneToOne(cmd: string, deps: set<Path>, exps: set<string>, paths: set<Path>)
  {
    forall e :: e in exps ==> Loc(cmd, deps, e) in paths
  }

  ghost predicate Post(cmd: string, deps: set<Path>, exps: set<string>, st: State)
  {
    forall e :: e in exps ==>
      Loc(cmd, deps, e) in DomSt(st) && GetSt(Loc(cmd, deps, e), st) == Oracle(Loc(cmd, deps, e), st)
  }

  // Oracle is like an oracle, because for a given path and state, it flawlessly predicts the unique artifact
  // that may live at that path.  This is less magical than it seems, because Loc is injective,
  // and therefore one can extract a unique (cmd,deps,exp) from p, and it's not so hard to see
  // how the oracle may "know" the artifact that results from that.
  ghost function Oracle(p: Path, st: State): Artifact

  // The oracle never changes its mind.  Therefore, if st0 is extended into st1 only by following
  // what the oracle predicts, then no predictions change.
  lemma OracleProperty(p: Path, st0: State, st1: State)
    requires Extends(st0, st1);
    ensures Oracle(p, st0) == Oracle(p, st1);

  ghost predicate Extends(st: State, st': State)
  {
    DomSt(st) <= DomSt(st') &&
    (forall p :: p in DomSt(st) ==> GetSt(p, st') == GetSt(p, st)) &&
    (forall p :: p !in DomSt(st) && p in DomSt(st') ==> GetSt(p, st') == Oracle(p, st))
  }

  lemma Lemma_ExtendsTransitive(st0: State, st1: State, st2: State)
    requires Extends(st0, st1) && Extends(st1, st2);
    ensures Extends(st0, st2);
  {
    forall p { OracleProperty(p, st0, st1); }
  }


  /******* Grammar *******/
  datatype Program = Program(stmts: seq<Statement>)

  datatype Statement = stmtVariable(id: Identifier, expr: Expression) |
                       stmtReturn(ret: Expression)

  datatype Expression = exprLiteral(lit: Literal) | exprIdentifier(id: Identifier) |
                        exprIf(cond: Expression, ifTrue: Expression, ifFalse: Expression) |
                        exprAnd(conj0: Expression, conj1: Expression) |
                        exprOr(disj0: Expression, disj1: Expression) |
                        exprInvocation(fun: Expression, args: seq<Expression>) |
                        exprError(r: Reason)

  datatype Literal = litTrue | litFalse | litUndefined | litNull |
                     litNumber(num: int) | litString(str: string) |
                     litPrimitive(prim: Primitive) |
                     // Q(rustan): How can I check the type of elems?
                     // Q(rustan): What happens with the sets?
                     litArrOfPaths(paths: set<Path>) |
                     litArrOfStrings(strs: set<string>) |
                     litArray(arr: seq<Expression>)

  datatype Primitive = primCreatePath | primExec

  datatype Reason = rCompatibility | rValidity

  type Path(==,00,!new)
  ghost function Loc(cmd: string, deps: set<Path>, exp: string): Path

  type Artifact(00)
  type Identifier

  datatype Tuple<A, B> = Pair(fst: A, snd: B)

  /******* Values *******/
  ghost predicate Value(expr: Expression)
  {
    expr.exprLiteral?
  }

  /******* Semantics *******/

  /******* Function 'build' *******/
  ghost function build(prog: Program, st: State): Tuple<Expression, State>
    requires Legal(prog.stmts);
  {
    do(prog.stmts, st, EmptyEnv())
  }

  /******* Function 'do' *******/
  ghost function do(stmts: seq<Statement>, st: State, env: Env): Tuple<Expression, State>
    requires Legal(stmts) && ValidEnv(env);
  {
    var stmt := stmts[0];
    if stmt.stmtVariable? then
      var Pair(expr', st') := eval(stmt.expr, st, env);
      if Value(expr') then
        var env' := SetEnv(stmt.id, expr', env);
        if Legal(stmts[1..]) then
          do(stmts[1..], st', env')
        else
          Pair(expr', st')
      else
        Pair(exprError(rValidity), st)
    // todo(maria): Add the recursive case.
    else
      eval(stmt.ret, st, env)
  }

  ghost predicate Legal(stmts: seq<Statement>)
  {
    |stmts| != 0
  }

  /******* Function 'eval' *******/
  ghost function eval(expr: Expression, st: State, env: Env): Tuple<Expression, State>
     requires ValidEnv(env);
     decreases expr;
  {
    if Value(expr) then
      Pair(expr, st)
    // identifier
    else if expr.exprIdentifier? then
      Pair(GetEnv(expr.id, env), st)
    // if-expression
    else if expr.exprIf? then
      var Pair(cond', st') := eval(expr.cond, st, env);
      if cond'.exprLiteral? && cond'.lit == litTrue then
        eval(expr.ifTrue, st', env)
      else if cond'.exprLiteral? && cond'.lit == litFalse then
        eval(expr.ifFalse, st', env)
      else
        Pair(exprError(rValidity), st)  // todo: should this be st' (and same for the error cases below)?
    // and-expression
    else if expr.exprAnd? then
      var Pair(conj0', st') := eval(expr.conj0, st, env);
      if conj0'.exprLiteral? && conj0'.lit == litTrue then
        eval(expr.conj1, st', env)
      else if conj0'.exprLiteral? && conj0'.lit == litFalse then
        Pair(exprLiteral(litFalse), st')
      else
        Pair(exprError(rValidity), st)
    // or-expression
    else if expr.exprOr? then
      var Pair(disj0', st') := eval(expr.disj0, st, env);
      if disj0'.exprLiteral? && disj0'.lit == litTrue then
        Pair(exprLiteral(litTrue), st')
      else if disj0'.exprLiteral? && disj0'.lit == litFalse then
        eval(expr.disj1, st', env)
      else
        Pair(exprError(rValidity), st)
    // invocation
    else if expr.exprInvocation? then
      var Pair(fun', st') := eval(expr.fun, st, env);
      var Pair(args', sts') := evalArgs(expr, expr.args, st, env);
      var sts'' := {st'} + sts';
      if !Compatible(sts'') then
        Pair(exprError(rCompatibility), st)
      else
        var stCombined := Combine(sts'');
        // primitive functions
        if fun'.exprLiteral? && fun'.lit.litPrimitive? then
          // primitive function 'exec'
          if fun'.lit.prim.primExec? then
            if |args'| == Arity(primExec) && ValidArgs(primExec, args', stCombined) then
              var ps := exec(args'[0].lit.str, args'[1].lit.paths, args'[2].lit.strs, stCombined);
              Pair(exprLiteral(litArrOfPaths(ps.fst)), ps.snd)
            else
              Pair(exprError(rValidity), st)
          else
          // primitive function 'createPath'
          // todo(maria): Add primitive function 'createPath'.
            Pair(exprError(rValidity), st)
        // todo(maria): Add non-primitive invocations.
        else
          Pair(exprError(rValidity), st)
    // error
    else
      Pair(exprError(rValidity), st)
  }

  ghost function evalArgs(context: Expression, args: seq<Expression>, stOrig: State, env: Env): Tuple<seq<Expression>, set<State>>
    requires
      ValidEnv(env) &&
      forall arg :: arg in args ==> arg < context;
    decreases context, |args|;
  {
    if args == [] then
      Pair([], {})
    else
      var r := eval(args[0], stOrig, env);
      var rr := evalArgs(context, args[1..], stOrig, env);
      Pair([r.fst] + rr.fst, {r.snd} + rr.snd)
  }

  ghost function Arity(prim: Primitive): nat
  {
    match prim
    case primCreatePath => 1
    case primExec => 3
  }

  ghost predicate ValidArgs(prim: Primitive, args: seq<Expression>, st: State)
    requires prim.primExec? ==> |args| == 3;
    requires prim.primCreatePath? ==> |args| == 1;
  {
    match prim
    case primCreatePath => false
    case primExec =>
      var cmd, deps, exps := args[0], args[1], args[2];
      cmd.exprLiteral? && cmd.lit.litString? &&
      deps.exprLiteral? && deps.lit.litArrOfPaths? &&
      exps.exprLiteral? && exps.lit.litArrOfStrings? &&
      deps.lit.paths <= DomSt(st) &&
      Pre(cmd.lit.str, deps.lit.paths, exps.lit.strs, st)
  }

  /******* Parallel builds are race-free *******/
  lemma ParallelBuildsTheorem(prog: Program, st: State)
    requires Legal(prog.stmts) && ValidState(st);
    ensures
      var Pair(expr', st') := build(prog, st);
      ValidState(st') &&
      (expr'.exprError? ==> expr'.r == rValidity);
  {
    var _, _ := BuildLemma(prog, st);
  }

  lemma BuildLemma(prog: Program, st: State) returns (expr': Expression, st': State)
    requires Legal(prog.stmts) && ValidState(st);
    ensures
      build(prog, st) == Pair(expr', st') &&
      ValidState(st') &&
      Extends(st, st') &&
      (expr'.exprError? ==> expr'.r == rValidity);
  {
    var result := build(prog, st);
    expr', st' := result.fst, result.snd;
    var _, _ := DoLemma(prog.stmts, st, EmptyEnv());
  }

  lemma DoLemma(stmts: seq<Statement>, st: State, env: Env) returns (expr': Expression, st': State)
    requires Legal(stmts) && ValidState(st) && ValidEnv(env);
    ensures
      Pair(expr', st') == do(stmts, st, env) &&
      ValidState(st') &&
      Extends(st, st') &&
      (expr'.exprError? ==> expr'.r == rValidity);
  {
    var result := do(stmts, st, env);
    expr', st' := result.fst, result.snd;
    var stmt := stmts[0];
    if stmt.stmtVariable? {
      var expr', st' := EvalLemma(stmt.expr, st, env);
      if Value(expr') {
        var env' := SetEnv(stmt.id, expr', env);
        if Legal(stmts[1..]) {
          var _, st'' := DoLemma(stmts[1..], st', env');
          Lemma_ExtendsTransitive(st, st', st'');
        } else {
        }
      } else { }
    } else {
      assert stmt.stmtVariable? || stmt.stmtReturn?;
      var _, _ := EvalLemma(stmt.ret, st, env);
    }
  }

  lemma EvalLemma(expr: Expression, st: State, env: Env) returns (expr': Expression, st': State)
    requires ValidState(st) && ValidEnv(env);
    ensures
      Pair(expr', st') == eval(expr, st, env) &&
      ValidState(st') &&
      Extends(st, st') &&
      (expr'.exprError? ==> expr'.r == rValidity);
    decreases expr;
  {
    var result := eval(expr, st, env);
    expr', st' := result.fst, result.snd;
    if Value(expr) {
    } else if expr.exprIdentifier? {
    } else if expr.exprIf? {
      var cond', st' := EvalLemma(expr.cond, st, env);
      if cond'.exprLiteral? && cond'.lit == litTrue {
        var _, st'' := EvalLemma(expr.ifTrue, st', env);
        Lemma_ExtendsTransitive(st, st', st'');
      } else if cond'.exprLiteral? && cond'.lit == litFalse {
        var _, st'' := EvalLemma(expr.ifFalse, st', env);
        Lemma_ExtendsTransitive(st, st', st'');
      } else { }
    } else if expr.exprAnd? {
      var conj0', st' := EvalLemma(expr.conj0, st, env);
      if conj0'.exprLiteral? && conj0'.lit == litTrue {
        var _, st'' := EvalLemma(expr.conj1, st', env);
        Lemma_ExtendsTransitive(st, st', st'');
      } else if conj0'.exprLiteral? && conj0'.lit == litFalse {
      } else { }
    } else if expr.exprOr? {
      var disj0', st' := EvalLemma(expr.disj0, st, env);
      if disj0'.exprLiteral? && disj0'.lit == litTrue {
      } else if disj0'.exprLiteral? && disj0'.lit == litFalse {
        var _, st'' := EvalLemma(expr.disj1, st', env);
        Lemma_ExtendsTransitive(st, st', st'');
      } else { }
    } else if expr.exprInvocation? {
      var fun', st' := EvalLemma(expr.fun, st, env);
      var args', sts' := EvalArgsLemma(expr, expr.args, st, env);
      var sts'' := {st'} + sts';
      if Compatible(sts'') {
        var stCombined := Combine(sts'');
        Lemma_Combine(sts'', st);
        if fun'.exprLiteral? && fun'.lit.litPrimitive? {
          if fun'.lit.prim.primExec? {
            if |args'| == Arity(primExec) && ValidArgs(primExec, args', stCombined) {
              var cmd, deps, exp := args'[0].lit.str, args'[1].lit.paths, args'[2].lit.strs;
              ExecProperty(cmd, deps, exp, stCombined);
              var resultExec := exec(cmd, deps, exp, stCombined);
              var stExec := resultExec.snd;
              Lemma_ExtendsTransitive(st, stCombined, stExec);
            } else { }
          } else { }
        } else { }
      } else { }
    } else { }
  }

  lemma EvalArgsLemma(context: Expression, args: seq<Expression>, stOrig: State, env: Env) returns (args': seq<Expression>, sts': set<State>)
    requires
      ValidState(stOrig) && ValidEnv(env) &&
      forall arg :: arg in args ==> arg < context;
    ensures
      Pair(args', sts') == evalArgs(context, args, stOrig, env) &&
      forall st' :: st' in sts' ==> ValidState(st') && Extends(stOrig, st');
    decreases context, |args|;
  {
    if args == [] {
      args', sts' := [], {};
    } else {
      var rArg, rSts := EvalLemma(args[0], stOrig, env);
      var rrArg, rrSts := EvalArgsLemma(context, args[1..], stOrig, env);
      args', sts' := [rArg] + rrArg, {rSts} + rrSts;
    }
  }
} // module M0

abstract module M1 refines M0 {
  datatype State = StateCons(m: map<Path, Artifact>)

  ghost function GetSt(p: Path, st: State): Artifact
  {
    st.m[p]
  }

  ghost function DomSt(st: State): set<Path>
    ensures forall p :: p in DomSt(st) ==> p in st.m;
  {
    set p | p in st.m
  }

  // A tiny test harness, just to show that it is possible to call build(...)
  ghost method Main()
  {
    var calcC: string, calcH: Path, calcObj: string;
    var cmd := exprLiteral(litString(calcC));
    var deps := exprLiteral(litArrOfPaths({calcH}));
    var exps := exprLiteral(litArrOfStrings({calcObj}));
    var exec := exprInvocation(exprLiteral(litPrimitive(primExec)), [cmd, deps, exps]);

    var h;
    var st := StateCons(map[calcH := h]);

    assert calcH != Loc(calcC, {calcH}, calcObj) ==> ValidArgs(primExec, exec.args, st);

    var program := Program.Program([stmtReturn(exec)]);
    var result := build(program, st);
    var e, st' := result.fst, result.snd;
  }
}

// This module does the heavy lifting of the consistency proof.
abstract module M2 refines M1 {
  ghost function SetSt(p: Path, a: Artifact, st: State): State
  {
    StateCons(st.m[p := a])
  }

  ghost function Restrict(paths: set<Path>, st: State): map<Path, Artifact>
  {
    map p | p in paths && p in DomSt(st) :: GetSt(p, st)
  }
  lemma RestrictMonotonicity(paths: set<Path>, st0: State, st1: State)
    requires paths <= DomSt(st0) && Extends(st0, st1);
    ensures Restrict(paths, st0) == Restrict(paths, st1);
  {
  }

  ghost function PickOne<T>(s: set<T>): T
    requires s != {};
  {
    var x :| x in s; x
  }

  ghost predicate WellFounded(p: Path)
  {
    exists cert :: CheckWellFounded(p, cert)
  }
  ghost predicate CheckWellFounded(p: Path, cert: WFCertificate)
    decreases cert;
  {
    cert.p == p &&
    (forall d :: d in LocInv_Deps(p) ==> exists c :: c in cert.certs && c.p == d) &&
    (forall c :: c in cert.certs ==> CheckWellFounded(c.p, c))
  }
  datatype WFCertificate = Cert(p: Path, certs: set<WFCertificate>)


  // We take as a given the existence of a function that carries out the work of "exec".
  // Instead of reading the system state directly and restricting such reads to the
  // given set of dependencies, "RunTool" is not given the whole system state but only
  // a part of it, namely the part that has artifacts for the declared dependencies.
  ghost function RunTool(cmd: string, deps: map<Path, Artifact>, exp: string): Artifact

  ghost function exec(cmd: string, deps: set<Path>, exps: set<string>, st: State): Tuple<set<Path>, State>
  {
    execOne(cmd, deps, Restrict(deps, st), exps, st)
  }
  ghost function execOne(cmd: string, deps: set<Path>, restrictedState: map<Path, Artifact>, exps: set<string>, st: State): Tuple<set<Path>, State>
  {
    if exps == {} then
      Pair({}, st)
    else
      var exp := PickOne(exps);
      var Pair(paths, st') := execOne(cmd, deps, restrictedState, exps - {exp}, st);
      var p := Loc(cmd, deps, exp);
      Pair(paths + {p}, if p in DomSt(st') then st' else SetSt(p, RunTool(cmd, restrictedState, exp), st'))
  }

  lemma ExecProperty(cmd: string, deps: set<Path>, exps: set<string>, st: State)
  {
    ExecOneProperty(cmd, deps, Restrict(deps, st), exps, st);
  }
  lemma ExecOneProperty(cmd: string, deps: set<Path>, restrictedState: map<Path, Artifact>, exps: set<string>, st: State)
    requires
      ValidState(st) &&
      deps <= DomSt(st) &&
      Pre(cmd, deps, exps, st) &&
      restrictedState == Restrict(deps, st);
    ensures
      var result'' := execOne(cmd, deps, restrictedState, exps, st);
      var paths'', st'' := result''.fst, result''.snd;
      ValidState(st'') &&
      Extends(st, st'') &&
      OneToOne(cmd, deps, exps, paths'') &&
      Post(cmd, deps, exps, st'');
  {
    if exps == {} {
    } else {
      var exp := PickOne(exps);
      var rest := execOne(cmd, deps, restrictedState, exps - {exp}, st);
      var paths, st' := rest.fst, rest.snd;
      var p := Loc(cmd, deps, exp);
      var a := RunTool(cmd, restrictedState, exp);
      var paths'', st'' := paths + {p}, if p in DomSt(st') then st' else SetSt(p, a, st');
      ExecOneProperty(cmd, deps, restrictedState, exps - {exp}, st);
      assert execOne(cmd, deps, restrictedState, exps, st).snd == st'';

      calc ==> {
        true;
        { LocInjectivity(cmd, deps, exp); }
        LocInv_Deps(p) == deps;
        { ExecOne_Lemma0(p); }
        WellFounded(p);
        ValidState(st'');
      }

      forall
        ensures Extends(st', st'') && Extends(st, st'');
      {
        LocInjectivity(cmd, deps, exp);
        if p !in DomSt(st') {
          calc {
            a;
            // def. a
            RunTool(cmd, restrictedState, exp);
            // def. restrictedState
            RunTool(cmd, Restrict(deps, st), exp);
            { RestrictMonotonicity(deps, st, st'); }
            RunTool(cmd, Restrict(deps, st'), exp);
            { CollectRestrict_Lemma(p, GetCert(p), deps, st'); }
            RunTool(cmd, CollectDependencies(p, GetCert(p), deps, st'), exp);
            // we use LocInjectivity here
            RunTool(LocInv_Cmd(p), CollectDependencies(p, GetCert(p), LocInv_Deps(p), st'), LocInv_Exp(p));
            // def. OracleWF
            OracleWF(p, GetCert(p), st');
            { assert WellFounded(p); }
            Oracle(p, st');
          }
        }
        assert Extends(st', st'');
        Lemma_ExtendsTransitive(st, st', st'');
      }

      assert OneToOne(cmd, deps, exps, paths'');

      forall e | e in exps
        ensures Loc(cmd, deps, e) in DomSt(st'') && GetSt(Loc(cmd, deps, e), st'') == Oracle(Loc(cmd, deps, e), st'');
      {
        var p := Loc(cmd, deps, e);
        assert p in DomSt(st'');
        if p in DomSt(st') {
          calc {
            GetSt(p, st'');
            { assert p in DomSt(st') && Extends(st', st''); }
            GetSt(p, st');
            // (I don't fully understand this step, but evidently Dafny can do it)
            Oracle(p, st);
            { OracleProperty(p, st, st''); }
            Oracle(p, st'');
          }
        } else {
          calc {
            GetSt(p, st'');
            RunTool(cmd, restrictedState, exp);
            RunTool(cmd, Restrict(deps, st), exp);
            // ?  -- I'm amazed!  How can it prove this step automatically?
            Oracle(p, st);
            { OracleProperty(p, st, st''); }
            Oracle(p, st'');
          }
        }
      }
    }
  }
  lemma ExecOne_Lemma0(p: Path)
    requires forall d :: d in LocInv_Deps(p) ==> WellFounded(d);
    ensures WellFounded(p);
  {
    var certs := set d | d in LocInv_Deps(p) :: GetCert(d);
    assert CheckWellFounded(p, Cert(p, certs));
  }
  ghost function GetCert(p: Path): WFCertificate
    requires WellFounded(p);
    ensures CheckWellFounded(p, GetCert(p));
  {
    var c :| CheckWellFounded(p, c);
    c
  }

  // Loc is injective.  Here are its inverse functions:
  ghost function LocInv_Cmd(p: Path): string
  ghost function LocInv_Deps(p: Path): set<Path>
  ghost function LocInv_Exp(p: Path): string
  lemma LocInjectivity(cmd: string, deps: set<Path>, exp: string)
    ensures LocInv_Cmd(Loc(cmd, deps, exp)) == cmd;
    ensures LocInv_Deps(Loc(cmd, deps, exp)) == deps;
    ensures LocInv_Exp(Loc(cmd, deps, exp)) == exp;

  ghost function Oracle(p: Path, st: State): Artifact
  {
    if WellFounded(p) then OracleWF(p, GetCert(p), st) else OracleArbitrary(p)
  }
  ghost function OracleArbitrary(p: Path): Artifact
  {
    var a :| true;
    a  // return an arbitrary artifact (note, the same "a" will be used for every call to function OracleArbitrary(p) for the same "p")
  }
  ghost function OracleWF(p: Path, cert: WFCertificate, st: State): Artifact
    requires CheckWellFounded(p, cert);
    decreases cert, 1;
  {
    var cmd, deps, e := LocInv_Cmd(p), LocInv_Deps(p), LocInv_Exp(p);
    RunTool(cmd, CollectDependencies(p, cert, deps, st), e)
  }
  ghost function CollectDependencies(p: Path, cert: WFCertificate, deps: set<Path>, st: State): map<Path, Artifact>
    requires CheckWellFounded(p, cert) && deps == LocInv_Deps(p);
    decreases cert, 0;
  {
    map d | d in deps :: if d in DomSt(st) then GetSt(d, st) else OracleWF(d, FindCert(d, cert.certs), st)
  }
  ghost function FindCert(d: Path, certs: set<WFCertificate>): WFCertificate
    requires exists c :: c in certs && c.p == d;
  {
    var c :| c in certs && c.p == d;
    c
  }

  // A well-founded path has a certificate, but certificates are not unique.  However, OracleWF gives the same value
  // for any cerificate for the path.
  lemma OracleWF_CertificateInsensitivity(p: Path, cert0: WFCertificate, cert1: WFCertificate, st: State)
    requires CheckWellFounded(p, cert0) && CheckWellFounded(p, cert1);
    ensures OracleWF(p, cert0, st) == OracleWF(p, cert1, st);
    decreases cert0, 1;
  {
    Collect_CertificateInsensitivity(p, cert0, cert1, LocInv_Deps(p), st);
  }
  lemma Collect_CertificateInsensitivity(p: Path, cert0: WFCertificate, cert1: WFCertificate, deps: set<Path>, st: State)
    requires CheckWellFounded(p, cert0) && CheckWellFounded(p, cert1) && deps == LocInv_Deps(p);
    ensures CollectDependencies(p, cert0, deps, st) == CollectDependencies(p, cert1, deps, st);
    decreases cert0, 0;
  {
    forall d | d in deps { OracleWF_CertificateInsensitivity(d, FindCert(d, cert0.certs), FindCert(d, cert1.certs), st); }
  }

  lemma CollectRestrict_Lemma(p: Path, cert: WFCertificate, deps: set<Path>, st: State)
    requires ValidState(st) && deps <= DomSt(st);
    requires CheckWellFounded(p, cert) && deps == LocInv_Deps(p);
    ensures CollectDependencies(p, cert, deps, st) == Restrict(deps, st);
  {
    var a, b := CollectDependencies(p, cert, deps, st), Restrict(deps, st);
    assert (set q | q in a) == deps == (set q | q in b);
    forall d | d in deps
      ensures a[d] == b[d];
    {
      calc {
        a[d];
        if d in DomSt(st) then GetSt(d, st) else OracleWF(d, FindCert(d, cert.certs), st);
        { assert d in DomSt(st); }
        GetSt(d, st);
        b[d];
      }
    }
  }

  lemma OracleProperty(p: Path, st0: State, st1: State)
    // This is the inherited specification:
    // requires Extends(st0, st1);
    // ensures Oracle(p, st0) == Oracle(p, st1);
  {
    if !WellFounded(p) {
      // trivial
    } else {
      var cert := GetCert(p);
      OracleWF_Property(p, cert, st0, st1);
    }
  }
  lemma OracleWF_Property(p: Path, cert: WFCertificate, st0: State, st1: State)
    requires Extends(st0, st1) && CheckWellFounded(p, cert);
    ensures OracleWF(p, cert, st0) == OracleWF(p, cert, st1);
    decreases cert, 1;
  {
    var cmd, deps, e := LocInv_Cmd(p), LocInv_Deps(p), LocInv_Exp(p);
    CollectProperty(p, cert, deps, st0, st1);
  }
  lemma CollectProperty(p: Path, cert: WFCertificate, deps: set<Path>, st0: State, st1: State)
    requires Extends(st0, st1) && CheckWellFounded(p, cert) && deps == LocInv_Deps(p);
    ensures CollectDependencies(p, cert, deps, st0) == CollectDependencies(p, cert, deps, st1);
    decreases cert, 0;
  {
    forall d | d in deps
      ensures (if d in DomSt(st0) then GetSt(d, st0) else OracleWF(d, FindCert(d, cert.certs), st0)) ==
              (if d in DomSt(st1) then GetSt(d, st1) else OracleWF(d, FindCert(d, cert.certs), st1));
    {
      if d in DomSt(st0) {
        assert d in DomSt(st1);
      } else if d in DomSt(st1) {
        calc {
          if d in DomSt(st0) then GetSt(d, st0) else OracleWF(d, FindCert(d, cert.certs), st0);
          OracleWF(d, FindCert(d, cert.certs), st0);
          { // any certificate is as good as any other
            OracleWF_CertificateInsensitivity(d, FindCert(d, cert.certs), GetCert(d), st0);
          }
          OracleWF(d, GetCert(d), st0);
          { assert WellFounded(d); }
          if WellFounded(d) then OracleWF(d, GetCert(d), st0) else OracleArbitrary(d);
          Oracle(d, st0);
          { assert Extends(st0, st1); }
          GetSt(d, st1);
          if d in DomSt(st1) then GetSt(d, st1) else OracleWF(d, FindCert(d, cert.certs), st1);
        }
      } else {
        OracleWF_Property(d, FindCert(d, cert.certs), st0, st1);
      }
    }
  }
}

// Finally, this module defines any remaining opaque types and function bodies and proves any
// remaining lemmas about these.  The actual definitions are not so interesting and are not meant
// to suggest that a deployed CloudMake use these definitions.  Rather, these definitions are here
// only to establish mathematical feasibility of previously axiomatized properties.
module M3 refines M2 {
  ghost function Union(st: State, st': State): State
  {
    StateCons(map p | p in DomSt(st) + DomSt(st') :: GetSt(p, if p in DomSt(st) then st else st'))
  }

  ghost function RunTool(cmd: string, deps: map<Path, Artifact>, exp: string): Artifact
  {
    // return an arbitrary artifact
    var a :| true;
    a
  }

  datatype Artifact = ArtifactCons(int)
  datatype Identifier = IdentifierCons(int)

  datatype Path =
    InternalPath(cmd: string, deps: set<Path>, exp: string) |
    ExternalPath(string)
  ghost function createPath(fn: string): Path
  {
    ExternalPath(fn)
  }
  lemma PathProperty(fn: string, fn': string)
  {
  }
  ghost function Loc(cmd: string, deps: set<Path>, exp: string): Path
  {
    InternalPath(cmd, deps, exp)
  }
  ghost function LocInv_Cmd(p: Path): string
  {
    match p
    case InternalPath(cmd, deps, exp) => cmd
    case ExternalPath(_) => var cmd :| true; cmd
  }
  ghost function LocInv_Deps(p: Path): set<Path>
  {
    match p
    case InternalPath(cmd, deps, exp) => deps
    case ExternalPath(_) => var deps :| true; deps
  }
  ghost function LocInv_Exp(p: Path): string
  {
    match p
    case InternalPath(cmd, deps, exp) => exp
    case ExternalPath(_) => var exp :| true; exp
  }
  lemma LocInjectivity(cmd: string, deps: set<Path>, exp: string)
  {
  }

  datatype Env = EnvCons(m: map<Identifier, Expression>)
  ghost function EmptyEnv(): Env
  {
    EnvCons(map[])
  }
  ghost function GetEnv(id: Identifier, env: Env): Expression
  {
    if id in env.m then env.m[id] else var lit :| true; exprLiteral(lit)
  }
  ghost function SetEnv(id: Identifier, expr: Expression, env: Env): Env
  {
    EnvCons(env.m[id := expr])
  }
  ghost predicate ValidEnv(env: Env)
  {
    forall id :: id in env.m ==> Value(env.m[id])
  }
}
