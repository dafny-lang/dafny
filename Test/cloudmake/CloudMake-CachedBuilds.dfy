// RUN: %dafny /compile:0 /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This module proves the correctness of the algorithms.  It leaves a number of things undefined.
// They are defined in refinement modules below.
abstract module M0 {
  /******* State *******/
  type State(!new)
  ghost function DomSt(st: State): set<Path>
  ghost function GetSt(p: Path, st: State): Artifact
    requires p in DomSt(st);

  // cached part of state
  type HashValue
  ghost function DomC(st: State): set<HashValue>
  ghost function Hash(p: Path): HashValue
  /* Note, in this version of the formalization and proof, we only record which things are in the
     cache.  The actual cache values can be retrieved from the system state.
  type Cmd
  ghost function GetC(h: HashValue, st: State): Cmd
  */
  ghost function UpdateC(cmd: string, deps: set<Path>, exps: set<string>, st: State): State
    ensures
      var st' := UpdateC(cmd, deps, exps, st);
      DomSt(st) == DomSt(st') && (forall p :: p in DomSt(st) ==> GetSt(p, st) == GetSt(p, st')) &&
      // The following is a rather weak property.  It only guarantees that the new things will be
      // in the cache, and that the cache remains consistent.  It says nothing else about what might
      // be in the cache or what happened to previous things in the cache.
      (ConsistentCache(st) ==> ConsistentCache(st')) &&
      forall e :: e in exps ==> Hash(Loc(cmd, deps, e)) in DomC(st');


  ghost predicate ValidState(st: State)
  {
    forall p :: p in DomSt(st) ==> WellFounded(p)
  }
  ghost predicate WellFounded(p: Path)

  // The specification given for this Union is liberal enough to allow incompatible
  // states, that is, st and st' are allowed to disagree on some paths.  Any such disagreement
  // will be resolved in favor of st.  For the purpose of supporting function Combine, we are
  // only ever interested in combining/unioning compatible states anyhow.
  ghost function Union(st: State, st': State, useCache: bool): State
    ensures
      var result := Union(st, st', useCache);
      DomSt(result) == DomSt(st) + DomSt(st') &&
      (forall p :: p in DomSt(result) ==>
        GetSt(p, result) == GetSt(p, if p in DomSt(st') then st' else st)) &&
      (useCache ==> DomC(result) == DomC(st) + DomC(st'));


  ghost predicate Compatible(sts: set<State>)
  {
    forall st, st' :: st in sts && st' in sts ==>
      forall p :: p in DomSt(st) && p in DomSt(st') ==> GetSt(p, st) == GetSt(p, st')
  }
  lemma CompatibleProperty(stOrig: State, sts: set<State>)
    requires forall s :: s in sts ==> Extends(stOrig, s);
    ensures Compatible(sts);
  {
    reveal Extends();
  }

  ghost function {:opaque} Combine(sts: set<State>, useCache: bool): State
    requires sts != {};
  {
    var st := PickOne(sts);
    if sts == {st} then
      st
    else
      Union(Combine(sts - {st}, useCache), st, useCache)
  }
  ghost function PickOne<T>(s: set<T>): T
    requires s != {};
  {
    var x :| x in s; x
  }

  lemma Lemma_Combine(sts: set<State>, parent: State, useCache: bool)
    requires
      sts != {} &&
      (forall st :: st in sts ==> ValidState(st) && Extends(parent, st)) &&
      (useCache ==> forall st :: st in sts ==> ConsistentCache(st));
    ensures
      var stCombined := Combine(sts, useCache);
      ValidState(stCombined) && Extends(parent, stCombined) &&
      (useCache ==>
        ConsistentCache(stCombined) &&
        (forall st :: st in sts ==> DomC(st) <= DomC(stCombined)) &&
        (forall h :: h in DomC(stCombined) ==> exists st :: st in sts && h in DomC(st)));
  {
    reveal Combine();
    var st := PickOne(sts);
    if sts == {st} {
    } else {
      var stCombined := Combine(sts, useCache);
      var smaller := sts - {st};
      var smallerCombination := Combine(smaller, useCache);
      assert stCombined == Union(smallerCombination, st, useCache);

      forall p | p !in DomSt(smallerCombination) && p in DomSt(stCombined)
        ensures GetSt(p, stCombined) == Oracle(p, smallerCombination);
      {
        reveal Extends();
        OracleProperty(p, parent, smallerCombination);
      }
      forall ensures Extends(smallerCombination, stCombined); {
        reveal Extends();
      }
      Lemma_ExtendsTransitive(parent, smallerCombination, stCombined);
    }
  }

  ghost predicate ConsistentCache(stC: State)
  {
    forall cmd, deps, e :: Hash(Loc(cmd, deps, e)) in DomC(stC) ==>
      Loc(cmd, deps, e) in DomSt(stC)
  }
  ghost predicate {:opaque} StateCorrespondence(st: State, stC: State)
  {
    // This definition, it turns out, is the same as Extends(st, stC)
    DomSt(st) <= DomSt(stC) &&
    (forall p :: p in DomSt(st) ==> GetSt(p, stC) == GetSt(p, st)) &&
    (forall p :: p !in DomSt(st) && p in DomSt(stC) ==> GetSt(p, stC) == Oracle(p, st))
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
      var result := exec(cmd, deps, exps, st);
      var paths, st' := result.fst, result.snd;
      ValidState(st') &&
      Extends(st, st') && ExtendsLimit(cmd, deps, exps, st, st') &&
      DomC(st) == DomC(st') &&  // no changes to the cache
      OneToOne(cmd, deps, exps, paths) &&
      Post(cmd, deps, exps, st');

  ghost predicate Pre(cmd: string, deps: set<Path>, exps: set<string>, st: State)
  {
    forall e :: e in exps ==>
      Loc(cmd, deps, e) in DomSt(st) ==> GetSt(Loc(cmd, deps, e), st) == Oracle(Loc(cmd, deps, e), st)
  }

  ghost predicate OneToOne(cmd: string, deps: set<Path>, exps: set<string>, paths: set<Path>)
  {
    // KRML:  The previous definition only gave a lower bound on the member inclusion in "paths":
    //    forall e :: e in exps ==> Loc(cmd, deps, e) in paths
    // but to compare "paths" with what's stored in the cache, we need to know exactly which
    // elements on in "paths".  So I strengthened the definition of OneToOne as follows:
    paths == set e | e in exps :: Loc(cmd, deps, e)
  }

  ghost predicate {:opaque} Post(cmd: string, deps: set<Path>, exps: set<string>, st: State)
  {
    forall e :: e in exps ==>
      Loc(cmd, deps, e) in DomSt(st) && GetSt(Loc(cmd, deps, e), st) == Oracle(Loc(cmd, deps, e), st)
  }

  ghost predicate ExtendsLimit(cmd: string, deps: set<Path>, exps: set<string>, st: State, st': State)
  {
    DomSt(st') == DomSt(st) + set e | e in exps :: Loc(cmd, deps, e)
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

  ghost predicate {:opaque} Extends(st: State, st': State)
  {
    DomSt(st) <= DomSt(st') &&
    (forall p :: p in DomSt(st) ==> GetSt(p, st') == GetSt(p, st)) &&
    (forall p :: p !in DomSt(st) && p in DomSt(st') ==> GetSt(p, st') == Oracle(p, st))
  }

  lemma Lemma_ExtendsTransitive(st0: State, st1: State, st2: State)
    requires Extends(st0, st1) && Extends(st1, st2);
    ensures Extends(st0, st2);
  {
    reveal Extends();
    forall p { OracleProperty(p, st0, st1); }
  }

  ghost function execC(cmd: string, deps: set<Path>, exps: set<string>, stC: State): Tuple<set<Path>, State>
  {
    if forall e | e in exps :: Hash(Loc(cmd, deps, e)) in DomC(stC) then
      var paths := set e | e in exps :: Loc(cmd, deps, e);
      Pair(paths, stC)
    else
      var result := exec(cmd, deps, exps, stC);
      var expr', st' := result.fst, result.snd;
      var stC' := UpdateC(cmd, deps, exps, st');
      Pair(expr', stC')
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

  datatype Reason = rCompatibility | rValidity | rInconsistentCache

  type Path(==,!new)
  ghost function Loc(cmd: string, deps: set<Path>, exp: string): Path

  type Artifact
  type Identifier

  datatype Tuple<A, B> = Pair(fst: A, snd: B)
  datatype Triple<A, B, C> = Tri(0: A, 1: B, 2: C)

  /******* Values *******/
  ghost predicate Value(expr: Expression)
  {
    expr.exprLiteral?
  }

  /******* Semantics *******/

  /******* Function 'build' *******/
  ghost function build(prog: Program, st: State, useCache: bool): Tuple<Expression, State>
    requires Legal(prog.stmts);
  {
    do(prog.stmts, st, EmptyEnv(), useCache)
  }

  /******* Function 'do' *******/
  ghost function do(stmts: seq<Statement>, st: State, env: Env, useCache: bool): Tuple<Expression, State>
    requires Legal(stmts) && ValidEnv(env);
  {
    var stmt := stmts[0];
    if stmt.stmtVariable? then
      var result := eval(stmt.expr, st, env, useCache);
      var expr', st' := result.fst, result.snd;
      if Value(expr') then
        var env' := SetEnv(stmt.id, expr', env);
        if Legal(stmts[1..]) then
          do(stmts[1..], st', env', useCache)
        else
          Pair(expr', st')
      else
        Pair(exprError(rValidity), st)
    // todo(maria): Add the recursive case.
    else
      eval(stmt.ret, st, env, useCache)
  }

  ghost predicate Legal(stmts: seq<Statement>)
  {
    |stmts| != 0
  }

  /******* Function 'eval' *******/
  ghost function {:opaque} eval(expr: Expression, st: State, env: Env, useCache: bool): Tuple<Expression, State>
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
      var result := eval(expr.cond, st, env, useCache);
      var cond', st' := result.fst, result.snd;
      if cond'.exprLiteral? && cond'.lit == litTrue then
        eval(expr.ifTrue, st', env, useCache)
      else if cond'.exprLiteral? && cond'.lit == litFalse then
        eval(expr.ifFalse, st', env, useCache)
      else
        Pair(exprError(rValidity), st)  // todo: should this be st' (and same for the error cases below)?
    // and-expression
    else if expr.exprAnd? then
      var result := eval(expr.conj0, st, env, useCache);
      var conj0', st' := result.fst, result.snd;
      if conj0'.exprLiteral? && conj0'.lit == litTrue then
        eval(expr.conj1, st', env, useCache)
      else if conj0'.exprLiteral? && conj0'.lit == litFalse then
        Pair(exprLiteral(litFalse), st')
      else
        Pair(exprError(rValidity), st)
    // or-expression
    else if expr.exprOr? then
      var result := eval(expr.disj0, st, env, useCache);
      var disj0', st' := result.fst, result.snd;
      if disj0'.exprLiteral? && disj0'.lit == litTrue then
        Pair(exprLiteral(litTrue), st')
      else if disj0'.exprLiteral? && disj0'.lit == litFalse then
        eval(expr.disj1, st', env, useCache)
      else
        Pair(exprError(rValidity), st)
    // invocation
    else if expr.exprInvocation? then
      var resultFun := eval(expr.fun, st, env, useCache);
      var fun', st' := resultFun.fst, resultFun.snd;
      var resultArgs := evalArgs(expr, expr.args, st, env, useCache);
      var args', sts' := resultArgs.fst, resultArgs.snd;
      var sts'' := {st'} + sts';
      if !Compatible(sts'') then
        Pair(exprError(rCompatibility), st)
      else
        var stCombined := Combine(sts'', useCache);
        // primitive functions
        if fun'.exprLiteral? && fun'.lit.litPrimitive? then
          // primitive function 'exec'
          if fun'.lit.prim.primExec? then
            if |args'| == Arity(primExec) && ValidArgs(primExec, args', stCombined) then
              var cmd, deps, exps := args'[0].lit.str, args'[1].lit.paths, args'[2].lit.strs;
              if !useCache then
                var ps := exec(cmd, deps, exps, stCombined);
                Pair(exprLiteral(litArrOfPaths(ps.fst)), ps.snd)
              else if ConsistentCache(stCombined) then
                var ps := execC(cmd, deps, exps, stCombined);
                Pair(exprLiteral(litArrOfPaths(ps.fst)), ps.snd)
              else
                Pair(exprError(rValidity), st)
            else
              Pair(exprError(rInconsistentCache), st)
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

  ghost function evalFunArgs(expr: Expression, st: State, env: Env, useCache: bool): Triple<Expression, seq<Expression>, set<State>>
    requires expr.exprInvocation? && ValidEnv(env);
  {
    var resultFun := eval(expr.fun, st, env, useCache);
    var fun', st' := resultFun.fst, resultFun.snd;
    var resultArgs := evalArgs(expr, expr.args, st, env, useCache);
    var args', sts' := resultArgs.fst, resultArgs.snd;
    var sts'' := {st'} + sts';
    Tri(fun', args', sts'')
  }

  lemma Lemma_EvalFunArgs_TwoState(expr: Expression, st: State, stC: State, env: Env, p: Triple<Expression, seq<Expression>, set<State>>, pC: Triple<Expression, seq<Expression>, set<State>>)
    requires expr.exprInvocation? && ValidState(st) && ValidState(stC) && ValidEnv(env);
    requires ConsistentCache(stC);
    requires StateCorrespondence(st, stC);
    requires p == evalFunArgs(expr, st, env, false);
    requires pC == evalFunArgs(expr, stC, env, true);
    ensures p.0 == pC.0 && p.1 == pC.1;
    decreases expr, 0;
  {
    var fun, funC := eval(expr.fun, st, env, false).fst, eval(expr.fun, stC, env, true).fst;
    var args, argsC := evalArgs(expr, expr.args, st, env, false).fst, evalArgs(expr, expr.args, stC, env, true).fst;

    assert fun == evalFunArgs(expr, st, env, false).0;
    assert args == evalFunArgs(expr, st, env, false).1;
    assert funC == evalFunArgs(expr, stC, env, true).0;
    assert argsC == evalFunArgs(expr, stC, env, true).1;

    var _, _, _ := Lemma_Eval(expr.fun, st, stC, env);
    var _, _, _ := Lemma_EvalArgs(expr, expr.args, st, stC, env);
  }

  lemma Lemma_EvalFunArgs_TwoState_StateCorrespondence(expr: Expression, st: State, stC: State, env: Env, p: Triple<Expression, seq<Expression>, set<State>>, pC: Triple<Expression, seq<Expression>, set<State>>)
    requires expr.exprInvocation? && ValidState(st) && ValidState(stC) && ValidEnv(env);
    requires ConsistentCache(stC);
    requires StateCorrespondence(st, stC);
    requires p == evalFunArgs(expr, st, env, false);
    requires pC == evalFunArgs(expr, stC, env, true);
    ensures StateCorrespondence(Combine(p.2, false), Combine(pC.2, true));
    decreases expr, 0;
  {
    var fun, funC := eval(expr.fun, st, env, false).fst, eval(expr.fun, stC, env, true).fst;
    var args, argsC := evalArgs(expr, expr.args, st, env, false).fst, evalArgs(expr, expr.args, stC, env, true).fst;

    assert fun == evalFunArgs(expr, st, env, false).0;
    assert args == evalFunArgs(expr, st, env, false).1;
    assert funC == evalFunArgs(expr, stC, env, true).0;
    assert argsC == evalFunArgs(expr, stC, env, true).1;

    var _, stFun, stFunC := Lemma_Eval(expr.fun, st, stC, env);
    var _, stsArgs, stsArgsC := Lemma_EvalArgs(expr, expr.args, st, stC, env);
    assert p.2 == {stFun} + stsArgs;
    assert pC.2 == {stFunC} + stsArgsC;
    CompatibleProperty(st, p.2);
    CompatibleProperty(stC, pC.2);
    StateCorrespondence_Ctor(st, stFun, stsArgs, stFunC, stsArgsC);
  }

  lemma Lemma_EvalFunArgs(expr: Expression, st: State, env: Env, useCache: bool, sts'': set<State>)
    requires expr.exprInvocation? && ValidState(st) && ValidEnv(env);
    requires useCache ==> ConsistentCache(st);
    requires evalFunArgs(expr, st, env, useCache).2 == sts'';
    ensures Compatible(sts'');
    ensures forall s :: s in sts'' ==> ValidState(s) && Extends(st, s) && (useCache ==> ConsistentCache(s));
  {
    var resultFun := eval(expr.fun, st, env, useCache);
    var fun', st' := resultFun.fst, resultFun.snd;
    var resultArgs := evalArgs(expr, expr.args, st, env, useCache);
    var args', sts' := resultArgs.fst, resultArgs.snd;
    assert sts'' == {st'} + sts';

    forall
      ensures ValidState(st') && Extends(st, st');
      ensures useCache ==> ConsistentCache(st');
    {
      var _, _ := EvalLemma(expr.fun, st, env, useCache);
    }
    forall s | s in sts'
      ensures ValidState(s) && Extends(st, s);
      ensures useCache ==> ConsistentCache(s);
    {
      var _, _ := EvalArgsLemma(expr, expr.args, st, env, useCache);
    }
    assert forall s :: s in sts'' ==> s == st' || s in sts';
    assert forall s :: s in sts'' ==> Extends(st, s);
    CompatibleProperty(st, sts'');
  }

  lemma Equiv_SuperCore(expr: Expression, st: State, env: Env, useCache: bool)
    requires expr.exprInvocation? && ValidEnv(env);
    ensures eval(expr, st, env, useCache) == evalSuperCore(expr, st, env, useCache);
  {
    reveal eval();
  }

  ghost function evalSuperCore(expr: Expression, st: State, env: Env, useCache: bool): Tuple<Expression, State>
    requires expr.exprInvocation? && ValidEnv(env);
  {
    var tri := evalFunArgs(expr, st, env, useCache);
    var fun', args', sts'' := tri.0, tri.1, tri.2;
    evalCompatCheckCore(st, sts'', fun', args', useCache)
  }

  ghost function evalCompatCheckCore(stOrig: State, sts: set<State>, fun: Expression, args: seq<Expression>, useCache: bool): Tuple<Expression, State>
    requires sts != {};
  {
    if !Compatible(sts) then
      Pair(exprError(rCompatibility), stOrig)
    else
      var stCombined := Combine(sts, useCache);
      if fun.exprLiteral? && fun.lit.litPrimitive? then
        if fun.lit.prim.primExec? then
          evalCore(stOrig, stCombined, args, useCache)
        else
          Pair(exprError(rValidity), stOrig)
      else
        Pair(exprError(rValidity), stOrig)
  }

  ghost function evalCore(stOrig: State, stCombined: State, args: seq<Expression>, useCache: bool): Tuple<Expression, State>
  {
    if |args| == Arity(primExec) && ValidArgs(primExec, args, stCombined) then
      var cmd, deps, exps := args[0].lit.str, args[1].lit.paths, args[2].lit.strs;
      if !useCache then
        var ps := exec(cmd, deps, exps, stCombined);
        Pair(exprLiteral(litArrOfPaths(ps.fst)), ps.snd)
      else if ConsistentCache(stCombined) then
        var ps := execC(cmd, deps, exps, stCombined);
        Pair(exprLiteral(litArrOfPaths(ps.fst)), ps.snd)
      else
        Pair(exprError(rValidity), stOrig)
    else
      Pair(exprError(rInconsistentCache), stOrig)
  }

  ghost function evalArgs(context: Expression, args: seq<Expression>, stOrig: State, env: Env, useCache: bool):
           Tuple<seq<Expression>, set<State>>
    requires
      ValidEnv(env) &&
      forall arg :: arg in args ==> arg < context;
    decreases context, |args|;
  {
    if args == [] then
      Pair([], {})
    else
      var r := eval(args[0], stOrig, env, useCache);
      var rr := evalArgs(context, args[1..], stOrig, env, useCache);
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
  lemma ParallelBuildsTheorem(prog: Program, st: State, useCache: bool)
    requires Legal(prog.stmts) && ValidState(st);
    requires useCache ==> ConsistentCache(st);
    ensures
      var result := build(prog, st, useCache);
      var expr', st' := result.fst, result.snd;
      ValidState(st') &&
      (expr'.exprError? ==> expr'.r != rCompatibility);
  {
    BuildLemma(prog, st, useCache);
  }

  lemma BuildLemma(prog: Program, st: State, useCache: bool)
    requires Legal(prog.stmts) && ValidState(st);
    requires useCache ==> ConsistentCache(st);
    ensures
      var result := build(prog, st, useCache);
      var expr', st' := result.fst, result.snd;
      ValidState(st') &&
      Extends(st, st') &&
      (expr'.exprError? ==> expr'.r != rCompatibility);
  {
    DoLemma(prog.stmts, st, EmptyEnv(), useCache);
  }

  lemma DoLemma(stmts: seq<Statement>, st: State, env: Env, useCache: bool)
    requires Legal(stmts) && ValidState(st) && ValidEnv(env);
    requires useCache ==> ConsistentCache(st);
    ensures
      var result := do(stmts, st, env, useCache);
      var expr', st' := result.fst, result.snd;
      ValidState(st') &&
      Extends(st, st') &&
      (useCache ==> ConsistentCache(st)) &&
      (expr'.exprError? ==> expr'.r != rCompatibility);
  {
    var stmt := stmts[0];
    if stmt.stmtVariable? {
      var expr', st' := EvalLemma(stmt.expr, st, env, useCache);
      if Value(expr') {
        var env' := SetEnv(stmt.id, expr', env);
        if Legal(stmts[1..]) {
          DoLemma(stmts[1..], st', env', useCache);
          var st'' := do(stmts[1..], st', env', useCache).snd;
          Lemma_ExtendsTransitive(st, st', st'');
        } else {
        }
      } else {
        reveal Extends();
      }
    } else {
      assert stmt.stmtVariable? || stmt.stmtReturn?;
      var _, _ := EvalLemma(stmt.ret, st, env, useCache);
    }
  }

  lemma LittleEvalLemma(expr: Expression, st: State, env: Env, useCache: bool, outExpr: Expression, outSt: State)
    requires ValidState(st) && ValidEnv(env);
    requires useCache ==> ConsistentCache(st);
    requires eval(expr, st, env, useCache) == Pair(outExpr, outSt);
    ensures
      ValidState(outSt) &&
      Extends(st, outSt) &&
      (useCache ==> ConsistentCache(outSt)) &&
      (outExpr.exprError? ==> outExpr.r != rCompatibility);
  {
    var _, _ := EvalLemma(expr, st, env, useCache);
  }

  lemma {:induction false} {:timeLimit 30} EvalLemma(expr: Expression, st: State, env: Env, useCache: bool) returns (outExpr: Expression, outSt: State)
    requires ValidState(st) && ValidEnv(env);
    requires useCache ==> ConsistentCache(st);
    ensures
      eval(expr, st, env, useCache) == Pair(outExpr, outSt) &&
      ValidState(outSt) &&
      Extends(st, outSt) &&
      (useCache ==> ConsistentCache(outSt)) &&
      (outExpr.exprError? ==> outExpr.r != rCompatibility);
    decreases expr;
  {
    var result := eval(expr, st, env, useCache);
    outExpr, outSt := result.fst, result.snd;
    if Value(expr) {
      reveal eval();  reveal Extends();
    } else if expr.exprIdentifier? {
      reveal eval();  reveal Extends();
    } else if expr.exprIf? {
      reveal eval();
      var cond', st' := EvalLemma(expr.cond, st, env, useCache);
      if cond'.exprLiteral? && cond'.lit == litTrue {
        var _, st'' := EvalLemma(expr.ifTrue, st', env, useCache);
        Lemma_ExtendsTransitive(st, st', st'');
      } else if cond'.exprLiteral? && cond'.lit == litFalse {
        var _, st'' := EvalLemma(expr.ifFalse, st', env, useCache);
        Lemma_ExtendsTransitive(st, st', st'');
      } else {
        reveal Extends();
      }
    } else if expr.exprAnd? {
      reveal eval();
      var conj0', st' := EvalLemma(expr.conj0, st, env, useCache);
      if conj0'.exprLiteral? && conj0'.lit == litTrue {
        var _, st'' := EvalLemma(expr.conj1, st', env, useCache);
        Lemma_ExtendsTransitive(st, st', st'');
      } else if conj0'.exprLiteral? && conj0'.lit == litFalse {
      } else {
        reveal Extends();
      }
    } else if expr.exprOr? {
      reveal eval();
      var disj0', st' := EvalLemma(expr.disj0, st, env, useCache);
      if disj0'.exprLiteral? && disj0'.lit == litTrue {
      } else if disj0'.exprLiteral? && disj0'.lit == litFalse {
        var _, st'' := EvalLemma(expr.disj1, st', env, useCache);
        Lemma_ExtendsTransitive(st, st', st'');
      } else {
        reveal Extends();
      }
    } else if expr.exprInvocation? {
      reveal eval();
      reveal Extends();
      var fun', st' := EvalLemma(expr.fun, st, env, useCache);
      var args', sts' := EvalArgsLemma(expr, expr.args, st, env, useCache);
      var sts'' := {st'} + sts';
      CompatibleProperty(st, sts'');
      if Compatible(sts'') {
        var stCombined := Combine(sts'', useCache);
        Lemma_Combine(sts'', st, useCache);
        if fun'.exprLiteral? && fun'.lit.litPrimitive? {
          if fun'.lit.prim.primExec? {
            if |args'| == Arity(primExec) && ValidArgs(primExec, args', stCombined) {
              var cmd, deps, exps := args'[0].lit.str, args'[1].lit.paths, args'[2].lit.strs;
              if !useCache {
                ExecProperty(cmd, deps, exps, stCombined);
                var ps := exec(cmd, deps, exps, stCombined);
                Lemma_ExtendsTransitive(st, stCombined, ps.snd);
              } else if ConsistentCache(stCombined) {
                var ps := execC(cmd, deps, exps, stCombined);
                if forall e | e in exps :: Hash(Loc(cmd, deps, e)) in DomC(stCombined) {
                } else {
                  ExecProperty(cmd, deps, exps, stCombined);
                  var result := exec(cmd, deps, exps, stCombined);
                  var expr', st' := result.fst, result.snd;
                  Lemma_ExtendsTransitive(st, stCombined, st');
                  var stC' := UpdateC(cmd, deps, exps, st');
                  assert outExpr == exprLiteral(litArrOfPaths(expr')) && outSt == stC';
                  assert useCache ==> ConsistentCache(outSt);  // apparently needed as lemma, if Extends is opaque
                }
              } else { }
            } else { }
          } else { }
        } else { }
      } else { }
    } else {
      reveal eval();
      reveal Extends();
    }
  }

  lemma EvalArgsLemma(context: Expression, args: seq<Expression>, stOrig: State, env: Env, useCache: bool)
             returns (exprs: seq<Expression>, sts: set<State>)
    requires
      ValidState(stOrig) && ValidEnv(env) &&
      (useCache ==> ConsistentCache(stOrig)) &&
      forall arg :: arg in args ==> arg < context;
    ensures
      evalArgs(context, args, stOrig, env, useCache) == Pair(exprs, sts) &&
      forall st' :: st' in sts ==>
        ValidState(st') && Extends(stOrig, st') &&
        (useCache ==> ConsistentCache(st'));
    decreases context, |args|;
  {
    if args == [] {
      exprs, sts := [], {};
    } else {
      var a, st := EvalLemma(args[0], stOrig, env, useCache);
      exprs, sts := EvalArgsLemma(context, args[1..], stOrig, env, useCache);
      exprs, sts := [a] + exprs, {st} + sts;
    }
  }

  /******* Cached builds are equivalent to clean builds *******/
  lemma CachedBuildsTheorem(prog: Program, st: State, stC: State)
    requires
      Legal(prog.stmts) &&
      ValidState(st) &&
      ValidState(stC) && ConsistentCache(stC) &&
      StateCorrespondence(st, stC);
    ensures
      var Pair(_, st'), Pair(_, stC') := build(prog, st, false), build(prog, stC, true);
      StateCorrespondence(st', stC');
  {
    var _, _ := Lemma_Do(prog.stmts, st, stC, EmptyEnv());
  }

  lemma Lemma_Do(stmts: seq<Statement>, st: State, stC: State, env: Env) returns (st': State, stC': State)
    requires
      Legal(stmts) && ValidEnv(env) &&
      ValidState(st) &&
      ValidState(stC) && ConsistentCache(stC) &&
      StateCorrespondence(st, stC);
    ensures
      st' == do(stmts, st, env, false).snd &&
      stC' == do(stmts, stC, env, true).snd &&
      StateCorrespondence(st', stC');
  {
    var result, resultC := do(stmts, st, env, false), do(stmts, stC, env, true);
    st', stC' := result.snd, resultC.snd;
    var stmt := stmts[0];
    if stmt.stmtVariable? {
      var expr', st', stC' := Lemma_Eval(stmt.expr, st, stC, env);
      if Value(expr') {
        var env' := SetEnv(stmt.id, expr', env);
        if Legal(stmts[1..]) {
          var _, _ := Lemma_Do(stmts[1..], st', stC', env');
        } else { }
      } else { }
    } else {
      var _, _, _ := Lemma_Eval(stmt.ret, st, stC, env);
    }
  }

  lemma Lemma_Eval(expr: Expression, st: State, stC: State, env: Env) returns (outExpr: Expression, outSt: State, outStC: State)
    requires
      ValidState(st) && ValidEnv(env) &&
      ValidState(stC) && ConsistentCache(stC) &&
      StateCorrespondence(st, stC);
    ensures
      Pair(outExpr, outSt) == eval(expr, st, env, false) &&
      Pair(outExpr, outStC) == eval(expr, stC, env, true) &&
      ValidState(outSt) && Extends(st, outSt) &&
      ValidState(outStC) && Extends(stC, outStC) && ConsistentCache(outStC) &&
      StateCorrespondence(outSt, outStC);
    decreases expr;
  {
    var result, resultC := eval(expr, st, env, false), eval(expr, stC, env, true);
    outExpr, outSt, outStC := result.fst, result.snd, resultC.snd;
    if Value(expr) {
      reveal eval();
      reveal Extends();
    } else if expr.exprIdentifier? {
      reveal eval();
      reveal Extends();
    } else if expr.exprIf? {
      reveal eval();
      var cond', st', stC' := Lemma_Eval(expr.cond, st, stC, env);
      if cond'.exprLiteral? && cond'.lit == litTrue {
        var _, st'', stC'' := Lemma_Eval(expr.ifTrue, st', stC', env);
        Lemma_ExtendsTransitive(st, st', st'');
        Lemma_ExtendsTransitive(stC, stC', stC'');
      } else if cond'.exprLiteral? && cond'.lit == litFalse {
        var _, st'', stC'' := Lemma_Eval(expr.ifFalse, st', stC', env);
        Lemma_ExtendsTransitive(st, st', st'');
        Lemma_ExtendsTransitive(stC, stC', stC'');
      } else {
        reveal Extends();
      }
    } else if expr.exprAnd? {
      reveal eval();
      var conj0', st', stC' := Lemma_Eval(expr.conj0, st, stC, env);
      if conj0'.exprLiteral? && conj0'.lit == litTrue {
        var _, st'', stC'' := Lemma_Eval(expr.conj1, st', stC', env);
        Lemma_ExtendsTransitive(st, st', st'');
        Lemma_ExtendsTransitive(stC, stC', stC'');
      } else if conj0'.exprLiteral? && conj0'.lit == litFalse {
      } else {
        reveal Extends();
      }
    } else if expr.exprOr? {
      reveal eval();
      var disj0', st', stC' := Lemma_Eval(expr.disj0, st, stC, env);
      if disj0'.exprLiteral? && disj0'.lit == litTrue {
      } else if disj0'.exprLiteral? && disj0'.lit == litFalse {
        var _, st'', stC'' := Lemma_Eval(expr.disj1, st', stC', env);
        Lemma_ExtendsTransitive(st, st', st'');
        Lemma_ExtendsTransitive(stC, stC', stC'');
      } else {
        reveal Extends();
      }
    } else if expr.exprInvocation? {
      outExpr, outSt, outStC := Lemma_Eval_Invocation(expr, st, stC, env);
      LittleEvalLemma(expr, st, env, false, outExpr, outSt);
      LittleEvalLemma(expr, stC, env, true, outExpr, outStC);
    } else {
      reveal eval();
      reveal Extends();
    }
  }

  lemma {:induction false} Lemma_Eval_Invocation(expr: Expression, st: State, stC: State, env: Env) returns (outExpr: Expression, outSt: State, outStC: State)
    requires
      expr.exprInvocation? &&
      ValidState(st) && ValidEnv(env) &&
      ValidState(stC) && ConsistentCache(stC) &&
      StateCorrespondence(st, stC);
    ensures
      Pair(outExpr, outSt) == eval(expr, st, env, false) &&
      Pair(outExpr, outStC) == eval(expr, stC, env, true) &&
      StateCorrespondence(outSt, outStC);
    decreases expr, 1;
  {
    var tri := evalFunArgs(expr, st, env, false);
    var fun', args', sts'' := tri.0, tri.1, tri.2;
    var p := evalCompatCheckCore(st, sts'', fun', args', false);

    var triC := evalFunArgs(expr, stC, env, true);
    var funC', argsC', stsC'' := triC.0, triC.1, triC.2;
    var pC := evalCompatCheckCore(stC, stsC'', funC', argsC', true);

    outExpr, outSt, outStC := p.fst, p.snd, pC.snd;
    var outExprC := pC.fst;

    Equiv_SuperCore(expr, st, env, false);
    Equiv_SuperCore(expr, stC, env, true);
    assert Pair(outExpr, outSt) == eval(expr, st, env, false);
    assert Pair(outExprC, outStC) == eval(expr, stC, env, true);

    Lemma_EvalFunArgs(expr, st, env, false, sts'');
    assert Compatible(sts'');
    Lemma_EvalFunArgs(expr, stC, env, true, stsC'');
    assert Compatible(stsC'');

    Lemma_EvalFunArgs_TwoState(expr, st, stC, env, tri, triC);
    Lemma_EvalFunArgs_TwoState_StateCorrespondence(expr, st, stC, env, tri, triC);
    Continuation(p, st, sts'', pC, stC, stsC'', fun', args');

    CompatCheckCore_StateCorrespondence(st, sts'', stC, stsC'', funC', argsC');
  }

  lemma CompatCheckCore_StateCorrespondence(stOrig: State, sts: set<State>, stOrigC: State, stsC: set<State>, fun: Expression, args: seq<Expression>)
    requires ValidState(stOrig) && ValidState(stOrigC);
    requires StateCorrespondence(stOrig, stOrigC);
    requires sts != {} && stsC != {};
    requires Compatible(sts) && Compatible(stsC);
    requires forall s :: s in sts ==> ValidState(s) && Extends(stOrig, s);
    requires forall s :: s in stsC ==> ValidState(s) && Extends(stOrigC, s) && ConsistentCache(s);
    requires StateCorrespondence(Combine(sts, false), Combine(stsC, true));
    ensures StateCorrespondence(evalCompatCheckCore(stOrig, sts, fun, args, false).snd, evalCompatCheckCore(stOrigC, stsC, fun, args, true).snd);
  {
    var p, pC := evalCompatCheckCore(stOrig, sts, fun, args, false), evalCompatCheckCore(stOrigC, stsC, fun, args, true);
    var stCombined := Combine(sts, false);
    Lemma_Combine(sts, stOrig, false);
    var stCombinedC := Combine(stsC, true);
    Lemma_Combine(stsC, stOrigC, true);
    if fun.exprLiteral? && fun.lit.litPrimitive? && fun.lit.prim.primExec? {
      assert p.snd == evalCore(stOrig, stCombined, args, false).snd;
      assert pC.snd == evalCore(stOrigC, stCombinedC, args, true).snd;

      EvalCoreDeepen(p, stOrig, stCombined, pC, stOrigC, stCombinedC, fun, args);

      assert StateCorrespondence(p.snd, pC.snd);
    } else {
    }
  }

  lemma Continuation(p: Tuple<Expression, State>, st: State, sts'': set<State>,
                     pC: Tuple<Expression, State>, stC: State, stsC'': set<State>,
                     fun: Expression, args: seq<Expression>)
    requires sts'' != {} && Compatible(sts'');
    requires stsC'' != {} && Compatible(stsC'');
    requires p == evalCompatCheckCore(st, sts'', fun, args, false);
    requires pC == evalCompatCheckCore(stC, stsC'', fun, args, true);
    requires forall s :: s in sts'' ==> ValidState(s) && Extends(st, s);
    requires forall s :: s in stsC'' ==> ValidState(s) && Extends(stC, s) && ConsistentCache(s);
    requires StateCorrespondence(st, stC);
    requires StateCorrespondence(Combine(sts'', false), Combine(stsC'', true));
    ensures p.fst == pC.fst;
  {
    var outExpr, outExprC := p.fst, pC.fst;
    var stCombined := Combine(sts'', false);
    Lemma_Combine(sts'', st, false);
    var stCombinedC := Combine(stsC'', true);
    Lemma_Combine(stsC'', stC, true);
    assert ConsistentCache(stCombinedC);
    assert StateCorrespondence(stCombined, stCombinedC);

    assert p ==
      if fun.exprLiteral? && fun.lit.litPrimitive? then
        if fun.lit.prim.primExec? then
          evalCore(st, stCombined, args, false)
        else
          Pair(exprError(rValidity), st)
      else
        Pair(exprError(rValidity), st);
    assert pC ==
      if fun.exprLiteral? && fun.lit.litPrimitive? then
        if fun.lit.prim.primExec? then
          evalCore(stC, stCombinedC, args, true)
        else
          Pair(exprError(rValidity), stC)
      else
        Pair(exprError(rValidity), stC);

    if fun.exprLiteral? && fun.lit.litPrimitive? && fun.lit.prim.primExec? {
      assert p == evalCore(st, stCombined, args, false);
      assert pC == evalCore(stC, stCombinedC, args, true);
      EvalCoreDeepen(p, st, stCombined, pC, stC, stCombinedC, fun, args);
    } else {
      // trivial
    }
  }

  lemma EvalCoreDeepen(p: Tuple<Expression, State>, st: State, stCombined: State,
                       pC: Tuple<Expression, State>, stC: State, stCombinedC: State,
                       fun: Expression, args: seq<Expression>)
    requires p == evalCore(st, stCombined, args, false);
    requires pC == evalCore(stC, stCombinedC, args, true);
    requires ValidState(stCombined) && ValidState(stCombinedC);
    requires ConsistentCache(stCombinedC);
    requires StateCorrespondence(st, stC) && StateCorrespondence(stCombined, stCombinedC);
    ensures p.fst == pC.fst;
    ensures StateCorrespondence(p.snd, pC.snd);
  {
    assume |args| == Arity(primExec) ==>
      ValidArgs(primExec, args, stCombined) == ValidArgs(primExec, args, stCombinedC);  // TODO:  This will require some work!

    if |args| == Arity(primExec) && ValidArgs(primExec, args, stCombined) {
      var cmd, deps, exts := args[0].lit.str, args[1].lit.paths, args[2].lit.strs;
      var ps := exec(cmd, deps, exts, stCombined);
      var psC := execC(cmd, deps, exts, stCombinedC);
      assert p == Pair(exprLiteral(litArrOfPaths(ps.fst)), ps.snd);
      assert pC == Pair(exprLiteral(litArrOfPaths(psC.fst)), psC.snd);

      reveal Extends();
      reveal StateCorrespondence();
      ExecProperty(cmd, deps, exts, stCombined);
      assert Extends(stCombined, ps.snd);
      assert ExtendsLimit(cmd, deps, exts, stCombined, ps.snd);
      var newPaths := set e | e in exts :: Loc(cmd, deps, e);
      assert DomSt(p.snd) == DomSt(stCombined) + newPaths;
      if forall e | e in exts :: Hash(Loc(cmd, deps, e)) in DomC(stCombinedC) {
        var paths := set e | e in exts :: Loc(cmd, deps, e);
        assert psC.fst == paths;
        assert psC == Pair(paths, stCombinedC);
        assert ps.fst == psC.fst;
        assert psC.snd == stCombinedC;

        assert StateCorrespondence(stCombined, stCombinedC);
        assert DomSt(stCombined) <= DomSt(stCombinedC);  // follows from the previous line
        assert newPaths <= DomSt(stCombinedC);
        assert DomSt(p.snd) <= DomSt(pC.snd);
        forall pth | pth in DomSt(p.snd)
          ensures GetSt(pth, p.snd) == GetSt(pth, stCombinedC);
        {
          if pth in DomSt(stCombined) {
            // follows from StateCorrespondence(stCombined, stCombinedC)
          } else {
            assert pth in newPaths;
            assert exists e :: e in exts && pth == Loc(cmd, deps, e);
            var e :| e in exts && pth == Loc(cmd, deps, e);
            assert Post(cmd, deps, exts, p.snd);
            reveal Post();
            assert GetSt(pth, p.snd) == Oracle(pth, p.snd);
          }
        }
        Lemma_Extends_StateCorrespondence(stCombined, p.snd, stCombinedC);
        assert StateCorrespondence(ps.snd, stCombinedC);
      } else {
        var result := exec(cmd, deps, exts, stCombinedC);
        var expr', st' := result.fst, result.snd;
        var stC' := UpdateC(cmd, deps, exts, st');
        assert psC == Pair(expr', stC');
        assert psC.fst == expr' == result.fst;
        ExecProperty(cmd, deps, exts, stCombinedC);
        assert psC.fst == ps.fst;

        assert Extends(stCombined, ps.snd) && Extends(stCombinedC, stC');
        assert DomSt(ps.snd) <= DomSt(st') == DomSt(stC');
        forall pth | pth in DomSt(ps.snd)
          ensures GetSt(pth, ps.snd) == GetSt(pth, st');
        {
          if pth in DomSt(stCombined) {
          } else {
            assert pth in newPaths;
            assert exists e :: e in exts && pth == Loc(cmd, deps, e);
            var e :| e in exts && pth == Loc(cmd, deps, e);
            assert Post(cmd, deps, exts, p.snd);
            reveal Post();
            calc {
              GetSt(pth, p.snd);
              // by Post
              Oracle(pth, p.snd);
              { OracleProperty(pth, stCombined, p.snd); }
              Oracle(pth, stCombined);
              { OracleProperty(pth, stCombined, stCombinedC); }
              Oracle(pth, stCombinedC);
              { OracleProperty(pth, stCombinedC, st'); }
              Oracle(pth, st');
              // by Post
              GetSt(pth, st');
            }
          }
        }
        forall pth | pth !in DomSt(p.snd) && pth in DomSt(st')
          ensures GetSt(pth, st') == Oracle(pth, p.snd);
        {
          assert pth !in DomSt(stCombined);
          if pth in DomSt(stCombinedC) {
            calc {
              GetSt(pth, st');
              GetSt(pth, stCombinedC);
              Oracle(pth, stCombined);
              { OracleProperty(pth, stCombined, p.snd); }
              Oracle(pth, p.snd);
            }
          } else {
            assert GetSt(pth, st') == Oracle(pth, stCombinedC);
          }
        }
        assert StateCorrespondence(p.snd, st');
        assert StateCorrespondence(ps.snd, psC.snd);
      }

      assert ps.fst == psC.fst;  // this is the quintescensce of what needs to be proved
      assert StateCorrespondence(ps.snd, psC.snd);
    } else {
      assert p == Pair(exprError(rInconsistentCache), st);
      assert pC == Pair(exprError(rInconsistentCache), stC);
    }
  }

  lemma Lemma_Extends_StateCorrespondence(st: State, st': State, stC: State)
    requires Extends(st, st') && StateCorrespondence(st, stC) && DomSt(st') <= DomSt(stC);
    ensures StateCorrespondence(st', stC);
  {
    reveal Extends();
    reveal StateCorrespondence();
    forall p | p !in DomSt(st') && p in DomSt(stC)
      ensures GetSt(p, stC) == Oracle(p, st');
    {
      OracleProperty(p, st, st');
    }
  }



  lemma Lemma_EvalArgs(context: Expression, args: seq<Expression>, stOrig: State, stOrigC: State, env: Env)
              returns (exprs: seq<Expression>, sts: set<State>, stsC: set<State>)
    requires
      ValidState(stOrig) && ValidEnv(env) &&
      ValidState(stOrigC) && ConsistentCache(stOrigC) &&
      StateCorrespondence(stOrig, stOrigC) &&
      forall arg :: arg in args ==> arg < context;
    decreases context, 0, |args|;
    ensures
      Pair(exprs, sts) == evalArgs(context, args, stOrig, env, false) &&
      Pair(exprs, stsC) == evalArgs(context, args, stOrigC, env, true) &&
      (forall s :: s in sts ==> ValidState(s) && Extends(stOrig, s)) &&
      (forall sC :: sC in stsC ==> ValidState(sC) && Extends(stOrigC, sC) && ConsistentCache(sC)) &&
      (args == [] ==> sts == stsC == {}) &&
      (args != [] ==> sts != {} && stsC != {} && StateCorrespondence(Combine(sts, false), Combine(stsC, true)));
  {
    if args == [] {
      exprs, sts, stsC := [], {}, {};
    } else {
      var a, st, stC := Lemma_Eval(args[0], stOrig, stOrigC, env);
      exprs, sts, stsC := Lemma_EvalArgs(context, args[1..], stOrig, stOrigC, env);
      CompatibleProperty(stOrig, {st} + sts);
      CompatibleProperty(stOrigC, {stC} + stsC);
      StateCorrespondence_Ctor(stOrig, st, sts, stC, stsC);
      exprs, sts, stsC := [a] + exprs, {st} + sts, {stC} + stsC;
    }
  }

  ghost function DomSt_Union(sts: set<State>): set<Path>
  {
    if sts == {} then {} else
    var st := PickOne(sts); DomSt(st) + DomSt_Union(sts - {st})
  }
  lemma Combine_DomSt_X(sts: set<State>, useCache: bool)
    requires sts != {};
    ensures DomSt(Combine(sts, useCache)) == DomSt_Union(sts);
  {
    reveal Combine();
  }
  lemma DomSt_Union_Cons(st: State, sts: set<State>)
    ensures DomSt_Union({st} + sts) == DomSt(st) + DomSt_Union(sts);
  {
    var big := {st} + sts;
    if st in sts {
      assert forall states {:induction} :: st in states ==> DomSt(st) <= DomSt_Union(states);
      assert {st} + sts == sts;
    } else {
      var stPick := PickOne(big);
      if st == stPick {
        assert big - {stPick} == sts;
      } else {
        calc {
          DomSt_Union(big);
          { assert big - {stPick} == {st} + (sts - {stPick}); }
          DomSt(stPick) + DomSt_Union({st} + (sts - {stPick}));
          { DomSt_Union_Cons(st, sts - {stPick}); }
          DomSt(stPick) + DomSt(st) + DomSt_Union(sts - {stPick});
          DomSt(st) + DomSt(stPick) + DomSt_Union(sts - {stPick});
          { DomSt_Union_Cons(stPick, sts - {stPick}); }
          DomSt(st) + DomSt_Union({stPick} + (sts - {stPick}));
          { assert {stPick} + (sts - {stPick}) == sts; }
          DomSt(st) + DomSt_Union(sts);
        }
      }
    }
  }

  lemma Combine_DomSt(st: State, sts: set<State>, useCache: bool)
    requires sts != {};
    ensures DomSt(Combine({st} + sts, useCache)) == DomSt(st) + DomSt(Combine(sts, useCache));
  {
    var big := {st} + sts;
    if st in sts {
      assert big == sts;
      assert forall states {:induction} :: st in states ==> DomSt(st) <= DomSt_Union(states);
      Combine_DomSt_X(sts, useCache);
    } else {
      var stPick := PickOne(big);
      if stPick == st {
        Combine_DomSt_X(big, useCache);
        Combine_DomSt_X(sts, useCache);
      } else if {stPick} == sts {
        reveal Combine();
        assert Combine(sts, useCache) == stPick;
        Combine_DomSt_X(big, useCache);
      } else {
        // assert forall states :: st in states ==> DomSt_Union(states) == DomSt(st) + DomSt_Union(states - {st});
        // assert forall aa, bb :: DomSt_Union(aa + bb) == DomSt_Union(aa) + DomSt_Union(bb);
        reveal Combine();
        assert big == {stPick} + ({st} + (sts - {stPick}));
        calc {
          DomSt(Combine(big, useCache));
          { Combine_DomSt_X(big, useCache); }
          DomSt_Union(big);
          DomSt(stPick) + DomSt_Union(big - {stPick});
          { Combine_DomSt_X(big - {stPick}, useCache); }
          DomSt(stPick) + DomSt(Combine(big - {stPick}, useCache));
          { assert big - {stPick} == {st} + (sts - {stPick});
            Combine_DomSt(st, sts - {stPick}, useCache);
          }
          DomSt(stPick) + DomSt(st) + DomSt(Combine(big - {stPick} - {st}, useCache));
          { Combine_DomSt_X(big - {stPick} - {st}, useCache); }
          DomSt(stPick) + DomSt(st) + DomSt_Union(big - {stPick} - {st});
          DomSt(st) + DomSt(stPick) + DomSt_Union(big - {stPick} - {st});
          { DomSt_Union_Cons(stPick, big - {stPick} - {st}); }
          DomSt(st) + DomSt_Union({stPick} + (big - {stPick} - {st}));
          { assert {stPick} + (big - {stPick} - {st}) == big - {st} == sts; }
          DomSt(st) + DomSt_Union(sts);
          { Combine_DomSt_X(sts, useCache); }
          DomSt(st) + DomSt(Combine(sts, useCache));
        }
      }
    }
  }
  lemma {:timeLimit 15} StateCorrespondence_Ctor(stOrig: State, st: State, sts: set<State>, stC: State, stsC: set<State>)
    requires ValidState(st) && forall s :: s in sts ==> ValidState(s);
    requires Extends(stOrig, st) && forall s :: s in sts ==> Extends(stOrig, s);
    requires StateCorrespondence(st, stC);
    requires sts == {} <==> stsC == {};
    requires sts != {} && stsC != {} ==> StateCorrespondence(Combine(sts, false), Combine(stsC, true));
    requires Compatible({st} + sts) && Compatible({stC} + stsC);
    ensures StateCorrespondence(Combine({st} + sts, false), Combine({stC} + stsC, true));
  {
    reveal Combine();
    if sts == {} {
    } else {
      reveal StateCorrespondence();
      var a, b := Combine({st} + sts, false), Combine({stC} + stsC, true);
      assert Combine({st}, false) == st;
      assert Combine({stC}, true) == stC;

      calc {
        DomSt(a);
        { Combine_DomSt(st, sts, false); }
        DomSt(st) + DomSt(Combine(sts, false));
      <= { assert DomSt(Combine(sts, false)) <= DomSt(Combine(stsC, true)); }
        DomSt(st) + DomSt(Combine(stsC, true));
      <=
        DomSt(stC) + DomSt(Combine(stsC, true));
        { Combine_DomSt(stC, stsC, true); }
        DomSt(b);
      }
      assert DomSt(a) <= DomSt(b);

      forall p | p in DomSt(a)
        ensures GetSt(p, a) == GetSt(p, b);
      {
        var stRepr := Combine_Representative(p, {st} + sts, false);
        if stRepr == st {
          CompatiblePick(p, stC, {stC} + stsC, true);
        } else {
          assert stRepr in sts;
          CombineExpandsDomain(p, stRepr, sts, false);
          CompatiblePick(p, stRepr, sts, false);
          assert GetSt(p, a) == GetSt(p, stRepr) == GetSt(p, Combine(sts, false)) == GetSt(p, Combine(stsC, true));
          var stReprC := Combine_Representative(p, stsC, true);
          assert stReprC in {stC} + stsC;
          CombineExpandsDomain(p, stReprC, {stC} + stsC, true);
          CompatiblePick(p, stReprC, {stC} + stsC, true);
        }
      }
      forall p | p !in DomSt(a) && p in DomSt(b)
        ensures GetSt(p, b) == Oracle(p, a);
      {
        forall ensures p !in DomSt(st); {
          CombineExpandsDomain(p, st, {st} + sts, false);
        }
        var stReprC := Combine_Representative(p, {stC} + stsC, true);
        if stReprC == stC {
          calc {
            GetSt(p, b);
            // by Combine_Representative and stRepr==stC
            GetSt(p, stC);
            // by StateCorrespondence(st, stC);
            Oracle(p, st);
            { OracleProperty(p, stOrig, st); }
            Oracle(p, stOrig);
            { Lemma_Combine({st} + sts, stOrig, false);
              OracleProperty(p, stOrig, a);
            }
            Oracle(p, a);
          }
        } else {
          assert stReprC in stsC;
          calc {
            GetSt(p, b);
            GetSt(p, stReprC);
            { CombineExpandsDomain(p, stReprC, stsC, true);
              CompatiblePick(p, stReprC, stsC, true);
            }
            GetSt(p, Combine(stsC, true));
            { Combine_DomSt(st, sts, false);
              assert p !in DomSt(Combine(sts, false));
              assert p in DomSt(Combine(stsC, true));
            }
            Oracle(p, Combine(sts, false));
            { Lemma_Combine(sts, stOrig, false);
              OracleProperty(p, stOrig, Combine(sts, false));
            }
            Oracle(p, stOrig);
            { Lemma_Combine({st} + sts, stOrig, false);
              OracleProperty(p, stOrig, a);
            }
            Oracle(p, a);
          }
        }
      }
    }
  }

  lemma CompatiblePick(p: Path, st: State, sts: set<State>, useCache: bool)
    requires st in sts;
    requires Compatible(sts);
    requires p in DomSt(st) && p in DomSt(Combine(sts, useCache));
    ensures GetSt(p, Combine(sts, useCache)) == GetSt(p, st);
  {
    reveal Combine();
  }
  lemma Combine_Representative(p: Path, sts: set<State>, useCache: bool) returns (stRepr: State)
    requires sts != {} && p in DomSt(Combine(sts, useCache));
    ensures stRepr in sts && p in DomSt(stRepr) && GetSt(p, stRepr) == GetSt(p, Combine(sts, useCache));
  {
    reveal Combine();
    var stPick := PickOne(sts);
    if p in DomSt(stPick) {
      stRepr := stPick;
    } else {
      assert GetSt(p, Combine(sts, useCache)) == GetSt(p, Combine(sts - {stPick}, useCache));
      stRepr := Combine_Representative(p, sts - {stPick}, useCache);
    }
  }
  lemma CombineExpandsDomain(p: Path, st: State, sts: set<State>, useCache: bool)
    requires st in sts;
    ensures p in DomSt(st) ==> p in DomSt(Combine(sts, useCache));
  {
    reveal Combine();
  }

} // module M0
