// RUN: %dafny /compile:0 /dprint:"%t.dprint" /autoTriggers:0 /restartProver "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/******* State *******/
type State

ghost function GetSt(p: Path, st: State): Artifact
ghost function SetSt(p: Path, a: Artifact, st: State): State

ghost function DomSt(st: State): set<Path>

ghost function Restrict(paths: set<Path>, st: State): State
  requires paths <= DomSt(st)
  ensures
    var st' := Restrict(paths, st);
    DomSt(st') == paths && forall p :: p in paths ==> GetSt(p, st) == GetSt(p, st')

ghost function Union(st: State, st': State): State
  ensures
    var result := Union(st, st');
    DomSt(result) == DomSt(st) + DomSt(st') &&
    forall p :: p in DomSt(result) ==>
      (p in DomSt(st) ==> GetSt(p, result) == GetSt(p, st)) &&
      (p in DomSt(st') ==> GetSt(p, result) == GetSt(p, st'))

lemma StateEqualityProperty(st: State, st': State)
  requires DomSt(st) == DomSt(st')
  requires forall p :: p in DomSt(st) ==> GetSt(p, st) == GetSt(p, st')
  ensures st == st'

/******* Cached state *******/
datatype StateC = S(st: State, c: Cache)

ghost function EmptyCache(): Cache
  ensures DomC(EmptyCache()) == {}

ghost function GetC(h: HashValue, c: Cache): Triple<Expression, Expression, string>
ghost function SetC(h: HashValue, cmd: Triple<Expression, Expression, string>, c: Cache): Cache
  ensures DomC(SetC(h, cmd, c)) == DomC(c) + {h}

ghost function UpdateC(cmd: Expression, deps: Expression, exts: Expression, stC: StateC): StateC
  requires
    cmd.exprLiteral? && cmd.lit.litString? &&
    deps.exprLiteral? && deps.lit.litArrOfPaths? &&
    exts.exprLiteral? && exts.lit.litArrOfStrings?
  ensures
    var stC' := UpdateC(cmd, deps, exts, stC);
    var hashValues := set e | e in exts.lit.strs :: Hash(Loc(cmd, deps, e));
    stC'.st == stC.st &&
    DomC(stC.c) + hashValues == DomC(stC'.c)
  decreases exts.lit.strs
{
  var strs := exts.lit.strs;
  if strs == {} then
    stC
  else
    var e := Choose(strs);
    var c' := SetC(Hash(Loc(cmd, deps, e)), Trio(cmd, deps, e), stC.c);
    var exts' := exprLiteral(litArrOfStrings(strs - {e}));
    UpdateC(cmd, deps, exts', S(stC.st, c'))
}

lemma UpdateCLemma(cmd: Expression, deps: Expression, exts: Expression, stC: StateC)
  requires
    cmd.exprLiteral? && cmd.lit.litString? &&
    deps.exprLiteral? && deps.lit.litArrOfPaths? &&
    exts.exprLiteral? && exts.lit.litArrOfStrings? &&
    ConsistentCache(stC) &&
    forall e :: e in exts.lit.strs ==> Loc(cmd, deps, e) in DomSt(stC.st)
  ensures
    var stC' := UpdateC(cmd, deps, exts, stC);
    ConsistentCache(stC') &&
    forall e :: e in exts.lit.strs ==> Hash(Loc(cmd, deps, e)) in DomC(stC'.c)
  decreases exts.lit.strs
{
  var strs := exts.lit.strs;
  var stC' := UpdateC(cmd, deps, exts, stC);
  if strs == {} {
  } else {
    var e := Choose(strs);
    var c' := SetC(Hash(Loc(cmd, deps, e)), Trio(cmd, deps, e), stC.c);
    var exts' := exprLiteral(litArrOfStrings(strs - {e}));
    // note: This assertion is necessary.
    assert stC' == UpdateC(cmd, deps, exts', S(stC.st, c'));
    forall cmd', deps', e' | Hash(Loc(cmd', deps', e')) == Hash(Loc(cmd, deps, e)) {
      HashProperty(cmd', deps', e', cmd, deps, e);
    }
  }
}

ghost function Choose(ss: set<string>): string
  requires ss != {}
{
  var s :| s in ss; s
}

ghost function DomC(c: Cache): set<HashValue>

ghost function UnionC(stC: StateC, stC': StateC): StateC
  ensures
    var result := UnionC(stC, stC');
    DomSt(result.st) == DomSt(stC.st) + DomSt(stC'.st) &&
    (forall p :: p in DomSt(result.st) ==>
      (p in DomSt(stC.st) ==> GetSt(p, result.st) == GetSt(p, stC.st)) &&
      (p in DomSt(stC'.st) ==> GetSt(p, result.st) == GetSt(p, stC'.st))) &&
    DomC(result.c) == DomC(stC.c) + DomC(stC'.c) &&
    (forall h :: h in DomC(result.c) ==>
      (h in DomC(stC.c) ==> GetC(h, result.c) == GetC(h, stC.c)) &&
      (h in DomC(stC'.c) ==> GetC(h, result.c) == GetC(h, stC'.c)))

ghost predicate CompatibleC(stsC: set<StateC>)
{
  forall stC, stC', p, h ::
    stC in stsC && stC' in stsC &&
    p in DomSt(stC.st) && p in DomSt(stC'.st) &&
    h in DomC(stC.c) && h in DomC(stC'.c) ==>
      GetSt(p, stC.st) == GetSt(p, stC'.st) && GetC(h, stC.c) == GetC(h, stC'.c)
}

ghost function CombineC(stsC: set<StateC>): StateC
  requires stsC != {}
  ensures
    var stCombinedC := CombineC(stsC);
    (forall stC :: stC in stsC ==> DomSt(stC.st) <= DomSt(stCombinedC.st)) &&
    (forall stC, p :: stC in stsC && p in DomSt(stC.st) ==>
      GetSt(p, stC.st) == GetSt(p, stCombinedC.st)) &&
    (forall p :: p in DomSt(stCombinedC.st) ==> exists stC :: stC in stsC && p in DomSt(stC.st)) &&
    (forall stC :: stC in stsC ==> DomC(stC.c) <= DomC(stCombinedC.c)) &&
    (forall stC, h :: stC in stsC && h in DomC(stC.c) ==>
      GetC(h, stC.c) == GetC(h, stCombinedC.c)) &&
    (forall h :: h in DomC(stCombinedC.c) ==> exists stC :: stC in stsC && h in DomC(stC.c))
{
  var stC :| stC in stsC;
  if stsC == {stC} then
    stC
  else
    UnionC(stC, CombineC(stsC - {stC}))
}

lemma CombineCLemma(stsC: set<StateC>)
  requires stsC != {}
  requires forall stC :: stC in stsC ==> ConsistentCache(stC)
  ensures
   var stC' := CombineC(stsC);
   ConsistentCache(stC')
{
}

ghost predicate ConsistentCache(stC: StateC)
{
  forall cmd, deps, e :: Hash(Loc(cmd, deps, e)) in DomC(stC.c) ==>
    Loc(cmd, deps, e) in DomSt(stC.st)
}

/******* {true} init {consistent_cache} *******/
ghost function ClearCache(stC: StateC): StateC
  ensures
    var stC' := ClearCache(stC);
    // note: This follows directly from the definition.
    stC.st == stC'.st && DomC(stC'.c) == {} &&
    ConsistentCache(stC')
{
  S(stC.st, EmptyCache())
}

/******* Environment *******/
type Env

ghost function EmptyEnv(): Env
ghost function GetEnv(id: Identifier, env: Env): Expression
  ensures Value(GetEnv(id, env))
ghost function SetEnv(id: Identifier, expr: Expression, env: Env): Env
  requires Value(expr)

/******* Primitive function 'exec' *******/
ghost function exec(cmd: Expression, deps: Expression, exts: Expression, st: State): Tuple<Expression, State>

lemma ExecProperty(cmd: Expression, deps: Expression, exts: Expression, st: State)
  requires
    cmd.exprLiteral? && cmd.lit.litString? &&
    deps.exprLiteral? && deps.lit.litArrOfPaths? &&
    exts.exprLiteral? && exts.lit.litArrOfStrings? &&
    deps.lit.paths <= DomSt(st) &&
    Pre(cmd, deps, exts, Restrict(deps.lit.paths, st))
  ensures
    var result := exec(cmd, deps, exts, st);
    var expr', st' := result.fst, result.snd;
    expr'.exprLiteral? && expr'.lit.litArrOfPaths? &&
    expr'.lit.paths <= DomSt(st') &&
    // note: We need this for the precondition of Restrict.
    DomSt(st) <= DomSt(st') && st == Restrict(DomSt(st), st') &&
    OneToOne(cmd, deps, exts, expr') &&
    Post(cmd, deps, exts, Restrict(deps.lit.paths, st')) &&
    forall p :: p !in DomSt(st) && p in DomSt(st') ==> p.OpaquePath?

ghost predicate Pre(cmd: Expression, deps: Expression, exts: Expression, st: State)
  requires
    cmd.exprLiteral? && cmd.lit.litString? &&
    deps.exprLiteral? && deps.lit.litArrOfPaths? &&
    exts.exprLiteral? && exts.lit.litArrOfStrings?
{
  forall e :: e in exts.lit.strs ==>
    Loc(cmd, deps, e) in DomSt(st) ==> GetSt(Loc(cmd, deps, e), st) == Res(cmd, deps, e, st)
}

ghost predicate Post(cmd: Expression, deps: Expression, exts: Expression, st: State)
  requires
    cmd.exprLiteral? && cmd.lit.litString? &&
    deps.exprLiteral? && deps.lit.litArrOfPaths? &&
    exts.exprLiteral? && exts.lit.litArrOfStrings?
{
  forall e :: e in exts.lit.strs ==>
    Loc(cmd, deps, e) in DomSt(st) && GetSt(Loc(cmd, deps, e), st) == Res(cmd, deps, e, st)
}

ghost function Res(cmd: Expression, deps: Expression, ext: string, st: State): Artifact

ghost predicate OneToOne(cmd: Expression, deps: Expression, exts: Expression, paths: Expression)
  requires
    cmd.exprLiteral? && cmd.lit.litString? &&
    deps.exprLiteral? && deps.lit.litArrOfPaths? &&
    exts.exprLiteral? && exts.lit.litArrOfStrings? &&
    paths.exprLiteral? && paths.lit.litArrOfPaths?
{
  forall e :: e in exts.lit.strs ==> Loc(cmd, deps, e) in paths.lit.paths
}

ghost function Loc(cmd: Expression, deps: Expression, ext: string): Path

/******* Primitive function 'execC' *******/
ghost function execC(cmd: Expression, deps: Expression, exts: Expression, stC: StateC): Tuple<Expression, StateC>
  requires
    cmd.exprLiteral? && cmd.lit.litString? &&
    deps.exprLiteral? && deps.lit.litArrOfPaths? &&
    exts.exprLiteral? && exts.lit.litArrOfStrings?
{
  if forall e | e in exts.lit.strs :: Hash(Loc(cmd, deps, e)) in DomC(stC.c) then
    var paths := set e | e in exts.lit.strs :: Loc(cmd, deps, e);
    var expr' := exprLiteral(litArrOfPaths(paths));
    Pair(expr', stC)
  else
    var result := exec(cmd, deps, exts, stC.st);
    var expr', st' := result.fst, result.snd;
    var stC' := UpdateC(cmd, deps, exts, S(st', stC.c));
    Pair(expr', stC')
}

lemma ExecCProperty(cmd: Expression, deps: Expression, exts: Expression, stC: StateC)
  requires
    cmd.exprLiteral? && cmd.lit.litString? &&
    deps.exprLiteral? && deps.lit.litArrOfPaths? &&
    exts.exprLiteral? && exts.lit.litArrOfStrings? &&
    deps.lit.paths <= DomSt(stC.st) &&
    PreC(cmd, deps, exts, stC) &&
    ConsistentCache(stC)
  ensures
    var result := execC(cmd, deps, exts, stC);
    var expr', stC' := result.fst, result.snd;
    expr'.exprLiteral? && expr'.lit.litArrOfPaths? &&
    expr'.lit.paths <= DomSt(stC'.st) &&
    // note: We need this for the precondition of Restrict.
    DomSt(stC.st) <= DomSt(stC'.st) && stC.st == Restrict(DomSt(stC.st), stC'.st) &&
    OneToOne(cmd, deps, exts, expr') &&
    PostC(cmd, deps, exts, stC') &&
    (forall p :: p !in DomSt(stC.st) && p in DomSt(stC'.st) ==> p.OpaquePath?) &&
    ConsistentCache(stC')
{
  var result := execC(cmd, deps, exts, stC);
  var expr', stC' := result.fst, result.snd;
  if forall e | e in exts.lit.strs :: Hash(Loc(cmd, deps, e)) in DomC(stC.c) {
    StateEqualityProperty(stC.st, Restrict(DomSt(stC.st), stC'.st));
  } else {
    ExecProperty(cmd, deps, exts, stC.st);
    var execResult := exec(cmd, deps, exts, stC.st);
    var st' := execResult.snd;
    assert DomSt(stC.st) <= DomSt(st');
    StateEqualityProperty(stC'.st, st');
    UpdateCLemma(cmd, deps, exts, S(st', stC.c));
  }
}

ghost predicate PreC(cmd: Expression, deps: Expression, exts: Expression, stC: StateC)
  requires
    cmd.exprLiteral? && cmd.lit.litString? &&
    deps.exprLiteral? && deps.lit.litArrOfPaths? &&
    exts.exprLiteral? && exts.lit.litArrOfStrings? &&
    // note: We need this for the precondition of Restrict.
    deps.lit.paths <= DomSt(stC.st)
{
  Pre(cmd, deps, exts, Restrict(deps.lit.paths, stC.st)) &&
  forall e :: e in exts.lit.strs ==> Hash(Loc(cmd, deps, e)) in DomC(stC.c) ==>
    Loc(cmd, deps, e) in deps.lit.paths
}

ghost predicate PostC(cmd: Expression, deps: Expression, exts: Expression, stC: StateC)
  requires
    cmd.exprLiteral? && cmd.lit.litString? &&
    deps.exprLiteral? && deps.lit.litArrOfPaths? &&
    exts.exprLiteral? && exts.lit.litArrOfStrings? &&
    // note: We need this for the precondition of Restrict.
    deps.lit.paths <= DomSt(stC.st)
{
  Post(cmd, deps, exts, Restrict(deps.lit.paths, stC.st)) &&
  forall e :: e in exts.lit.strs ==> Hash(Loc(cmd, deps, e)) in DomC(stC.c)
}

ghost function Hash(p: Path): HashValue

lemma HashProperty(cmd: Expression, deps: Expression, ext: string, cmd': Expression, deps': Expression, ext': string)
  requires Hash(Loc(cmd, deps, ext)) == Hash(Loc(cmd', deps', ext'))
  ensures cmd == cmd' && deps == deps' && ext == ext'

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
                   litArrOfPaths(paths: set<Path>) |
                   litArrOfStrings(strs: set<string>) |
                   litArray(arr: seq<Expression>)

datatype Primitive = primCreatePath | primExec

datatype Reason = rCompatibility | rValidity | rInconsistentCache

datatype Path = OpaquePath(int) | TransparentPath(int)
type Artifact
type Identifier

type Cache
type HashValue

datatype Tuple<A, B> = Pair(fst: A, snd: B)
datatype Triple<A, B, C> = Trio(fst: A, snd: B, trd: C)

/******* Values *******/
ghost predicate Value(expr: Expression)
{
  expr.exprLiteral?
}

/******* Semantics *******/

ghost predicate Legal(stmts: seq<Statement>)
{
  |stmts| != 0
}

ghost function Arity(prim: Primitive): nat
{
  match prim
  case primCreatePath => 1
  case primExec => 3
}

/******* Function 'buildC' *******/
ghost function buildC(prog: Program, stC: StateC): Tuple<Expression, StateC>
  requires Legal(prog.stmts)
{
  doC(prog.stmts, stC, EmptyEnv())
}

/******* Function 'doC' *******/
ghost function doC(stmts: seq<Statement>, stC: StateC, env: Env): Tuple<Expression, StateC>
  requires Legal(stmts)
{
  var stmt := stmts[0];
  if stmt.stmtVariable? then
    var result := evalC(stmt.expr, stC, env);
    var expr', stC' := result.fst, result.snd;
    if Value(expr') then
      var env' := SetEnv(stmt.id, expr', env);
      if Legal(stmts[1..]) then
        doC(stmts[1..], stC', env')
      else
        Pair(expr', stC')
    else
      Pair(exprError(rValidity), stC)
  // todo(maria): Add the recursive case.
  else
    assert stmt.stmtVariable? || stmt.stmtReturn?;
    evalC(stmt.ret, stC, env)
}

/******* Function 'evalC' *******/
ghost function evalC(expr: Expression, stC: StateC, env: Env): Tuple<Expression, StateC>
  decreases expr
{
  if Value(expr) then
    Pair(expr, stC)
  // identifier
  else if expr.exprIdentifier? then
    Pair(GetEnv(expr.id, env), stC)
  // if-expression
  else if expr.exprIf? && expr.cond.exprLiteral? && expr.cond.lit == litTrue then
    evalC(expr.ifTrue, stC, env)
  else if expr.exprIf? && expr.cond.exprLiteral? && expr.cond.lit == litFalse then
    evalC(expr.ifFalse, stC, env)
  else if expr.exprIf? then
    var result := evalC(expr.cond, stC, env);
    var cond', stC' := result.fst, result.snd;
    if cond'.exprLiteral? && cond'.lit == litTrue then
      evalC(expr.ifTrue, stC', env)
    else if cond'.exprLiteral? && cond'.lit == litFalse then
      evalC(expr.ifFalse, stC', env)
    else
      Pair(exprError(rValidity), stC)
  // and-expression
  else if expr.exprAnd? then
    var result := evalC(expr.conj0, stC, env);
    var conj0', stC' := result.fst, result.snd;
    if conj0'.exprLiteral? && conj0'.lit == litTrue then
      evalC(expr.conj1, stC', env)
    else if conj0'.exprLiteral? && conj0'.lit == litFalse then
      Pair(exprLiteral(litFalse), stC')
    else
      Pair(exprError(rValidity), stC)
  // or-expression
  else if expr.exprOr? then
    var result := evalC(expr.disj0, stC, env);
    var disj0', stC' := result.fst, result.snd;
    if disj0'.exprLiteral? && disj0'.lit == litTrue then
      Pair(exprLiteral(litTrue), stC')
    else if disj0'.exprLiteral? && disj0'.lit == litFalse then
      evalC(expr.disj1, stC', env)
    else
      Pair(exprError(rValidity), stC)
  // invocation
  else if expr.exprInvocation? then
    var resultFun := evalC(expr.fun, stC, env);
    var fun', stC' := resultFun.fst, resultFun.snd;
    var resultArgs := evalArgsC(expr, expr.args, stC, env);
    var args', stsC' := resultArgs.fst, resultArgs.snd;
    var stsC'' := {stC'} + stsC';
    if CompatibleC(stsC'') then
      var stCombinedC := CombineC(stsC'');
      // primitive functions
      if fun'.exprLiteral? && fun'.lit.litPrimitive? then
        // primitive function 'execC'
        if fun'.lit.prim.primExec? then
          if |args'| == Arity(primExec) && ValidArgsC(primExec, args', stCombinedC) then
            execC(args'[0], args'[1], args'[2], stCombinedC)
          else
            if ConsistentCache(stCombinedC) then
              Pair(exprError(rValidity), stC)
            else
              Pair(exprError(rInconsistentCache), stC)
        else
        // primitive function 'createPath'
        // todo(maria): Add primitive function 'createPath'.
          Pair(exprError(rValidity), stC)
      // todo(maria): Add non-primitive invocations.
      else
        Pair(exprError(rValidity), stC)
    else
      Pair(exprError(rCompatibility), stC)
  // error
  else
    Pair(exprError(rValidity), stC)
}

ghost function evalArgsC(expr: Expression, args: seq<Expression>, stC: StateC, env: Env):
         Tuple<seq<Expression>, set<StateC>>
  requires forall arg :: arg in args ==> arg < expr
  decreases expr, |args| + 1

{
  evalArgsC'(expr, args, stC, env, [], {})
}

ghost function evalArgsC'(expr: Expression, args: seq<Expression>, stC: StateC, env: Env,
                    args': seq<Expression>, stsC': set<StateC>):
         Tuple<seq<Expression>, set<StateC>>
  requires forall arg :: arg in args ==> arg < expr
  decreases expr, |args|
{
  if args == [] then
    Pair(args', stsC')
  else
    var arg := args[0];
    var result := evalC(arg, stC, env);
    var arg', stC' := result.fst, result.snd;
    evalArgsC'(expr, args[1..], stC, env, args' + [arg'], stsC' + {stC'})
}

ghost predicate ValidArgsC(prim: Primitive, args: seq<Expression>, stC: StateC)
  requires prim.primExec? ==> |args| == 3
  requires prim.primCreatePath? ==> |args| == 1
{
  match prim
  case primCreatePath => false
  case primExec =>
    var cmd, deps, exts := args[0], args[1], args[2];
    cmd.exprLiteral? && cmd.lit.litString? &&
    deps.exprLiteral? && deps.lit.litArrOfPaths? &&
    exts.exprLiteral? && exts.lit.litArrOfStrings? &&
    deps.lit.paths <= DomSt(stC.st) &&
    PreC(cmd, deps, exts, stC)
}

/******* {consistent_cache} buildC {no_bad_cache_error /\ consistent_cache} *******/
lemma CachedBuildsTheorem(prog: Program, stC: StateC)
  requires Legal(prog.stmts)
  requires ConsistentCache(stC)
  ensures
    var result := buildC(prog, stC);
    var expr', stC' := result.fst, result.snd;
    ConsistentCache(stC') && expr'.exprError? ==>
    expr'.r != rInconsistentCache
{
  BuildCLemma(prog, stC);
}

lemma BuildCLemma(prog: Program, stC: StateC)
  requires Legal(prog.stmts)
  requires ConsistentCache(stC)
  ensures
    var result := buildC(prog, stC);
    var expr', stC' := result.fst, result.snd;
    ConsistentCache(stC') && (expr'.exprError? ==> expr'.r != rInconsistentCache)
{
  DoCLemma(prog.stmts, stC, EmptyEnv());
}

lemma DoCLemma(stmts: seq<Statement>, stC: StateC, env: Env)
  requires Legal(stmts)
  requires ConsistentCache(stC)
  ensures
    var result := doC(stmts, stC, env);
    var expr', stC' := result.fst, result.snd;
    ConsistentCache(stC') && (expr'.exprError? ==> expr'.r != rInconsistentCache)
{
  var stmt := stmts[0];
  if stmt.stmtVariable? {
    EvalCLemma(stmt.expr, stC, env);
    var result := evalC(stmt.expr, stC, env);
    var expr', stC' := result.fst, result.snd;
    if Value(expr') {
      var env' := SetEnv(stmt.id, expr', env);
      if Legal(stmts[1..]) {
        DoCLemma(stmts[1..], stC', env');
      } else { }
    } else { }
  // todo(maria): Add the recursive case.
  } else {
    assert stmt.stmtVariable? || stmt.stmtReturn?;
    EvalCLemma(stmt.ret, stC, env);
  }
}

lemma {:induction expr} EvalCLemma(expr: Expression, stC: StateC, env: Env)
  requires ConsistentCache(stC)
  ensures
    var result := evalC(expr, stC, env);
    var expr', stC' := result.fst, result.snd;
    ConsistentCache(stC') && (expr'.exprError? ==> expr'.r != rInconsistentCache)
  decreases expr
{
  if Value(expr) {
  } else if expr.exprIdentifier? {
  } else if expr.exprIf? && expr.cond.exprLiteral? && expr.cond.lit == litTrue {
  } else if expr.exprIf? && expr.cond.exprLiteral? && expr.cond.lit == litFalse {
  } else if expr.exprIf? {
    var result := evalC(expr.cond, stC, env);
    var cond', stC' := result.fst, result.snd;
    if cond'.exprLiteral? && cond'.lit == litTrue {
      EvalCLemma(expr.ifTrue, stC', env);
    } else if cond'.exprLiteral? && cond'.lit == litFalse {
      EvalCLemma(expr.ifFalse, stC', env);
    } else { }
  } else if expr.exprAnd? {
    var result := evalC(expr.conj0, stC, env);
    var conj0', stC' := result.fst, result.snd;
    if conj0'.exprLiteral? && conj0'.lit == litTrue {
      EvalCLemma(expr.conj1, stC', env);
    } else if conj0'.exprLiteral? && conj0'.lit == litFalse {
    } else { }
  } else if expr.exprOr? {
    var result := evalC(expr.disj0, stC, env);
    var disj0', stC' := result.fst, result.snd;
    if disj0'.exprLiteral? && disj0'.lit == litTrue {
    } else if disj0'.exprLiteral? && disj0'.lit == litFalse {
      EvalCLemma(expr.disj1, stC', env);
    } else { }
  } else if expr.exprInvocation? {
    EvalCLemma(expr.fun, stC, env);
    var resultFun := evalC(expr.fun, stC, env);
    var fun', stC' := resultFun.fst, resultFun.snd;
    EvalArgsCLemma(expr, expr.args, stC, env);
    var resultArgs := evalArgsC(expr, expr.args, stC, env);
    var args', stsC' := resultArgs.fst, resultArgs.snd;
    var stsC'' := {stC'} + stsC';
    if CompatibleC(stsC'') {
      CombineCLemma(stsC'');
      var stCombinedC := CombineC(stsC'');
      if fun'.exprLiteral? && fun'.lit.litPrimitive? {
        if fun'.lit.prim.primExec? {
          if |args'| == Arity(primExec) && ValidArgsC(primExec, args', stCombinedC) {
            ExecCProperty(args'[0], args'[1], args'[2], stCombinedC);
            var resultExec := execC(args'[0], args'[1], args'[2], stCombinedC);
            var stExecC := resultExec.snd;
            // note: This assertion is necessary.
            assert DomSt(stC'.st) <= DomSt(stCombinedC.st);
            forall p | p in DomSt(stCombinedC.st) && p in DomSt(stExecC.st)
              ensures GetSt(p, stCombinedC.st) == GetSt(p, stExecC.st)
            {
              assert DomSt(stCombinedC.st) <= DomSt(stExecC.st);
              assert stCombinedC.st == Restrict(DomSt(stCombinedC.st), stExecC.st);
            }
          } else {
            if ConsistentCache(stCombinedC) {
            } else { }
          }
        } else { }
      } else { }
    } else { }
  } else { }
}

lemma EvalArgsCLemma(expr: Expression, args: seq<Expression>, stC: StateC, env: Env)
  requires ConsistentCache(stC)
  requires forall arg :: arg in args ==> arg < expr
  ensures
    var result := evalArgsC(expr, args, stC, env);
    var stsC' := result.snd;
    forall stC' :: stC' in stsC' ==> ConsistentCache(stC')
  decreases expr, |args| + 1

{
  EvalArgsC'Lemma(expr, args, stC, env, [], {});
}

lemma EvalArgsC'Lemma(expr: Expression, args: seq<Expression>, stC: StateC, env: Env,
                             args': seq<Expression>, stsC': set<StateC>)
  requires ConsistentCache(stC)
  requires forall stC' :: stC' in stsC' ==> ConsistentCache(stC')
  requires forall arg :: arg in args ==> arg < expr
  ensures
    var result := evalArgsC'(expr, args, stC, env, args', stsC');
    var stsC'' := result.snd;
    forall stC'' :: stC'' in stsC'' ==> ConsistentCache(stC'')
  decreases expr, |args|
{
  if args == [] {
  } else {
    var arg := args[0];
    EvalCLemma(arg, stC, env);
    var result := evalC(arg, stC, env);
    var arg', stC' := result.fst, result.snd;
    EvalArgsC'Lemma(expr, args[1..], stC, env, args' + [arg'], stsC' + {stC'});
  }
}
