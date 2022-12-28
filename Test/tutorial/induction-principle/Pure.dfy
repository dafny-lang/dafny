// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "Utils.dfy"
include "AST.dfy"
include "Interp.dfy"
include "Induction.dfy"

module Pure refines Induction {
  // We write a small analysis which checks if an expression is pure (i.e., doesn't
  // have side effects).

  import opened Interp

  predicate method IsPure(e: Expr, locals: set<string> := {})
    decreases e
    // `locals`: the set of local variables which have been introduced by outer
    // let-bindings (if the expression only updates those variables then it is
    // pure, because those variables don't escape the scope of the term).
  {
    match e
      case Var(name) => true
      case Literal(n) => true
      case Bind(bvars, bvals, body) =>
        && IsPure_Es(bvals, locals)
        && IsPure(body, (set x | x in bvars) + locals)
      case Assign(avars, avals) =>
        (forall x | x in avars :: x in locals) && IsPure_Es(avals, locals)
      case If(cond, thn, els) =>
        && IsPure(cond, locals)
        && IsPure(thn, locals)
        && IsPure(els, locals)
      case Op(op, oe1, oe2) =>
        IsPure(oe1, locals) && IsPure(oe2, locals)
      case Seq(es) =>
        IsPure_Es(es, locals)
  }

  predicate method IsPure_Es(es: seq<Expr>, locals: set<string> := {})
    decreases es, 0
  {
    if es == [] then true
    else
      && IsPure(es[0], locals)
      && IsPure_Es(es[1..], locals)
  }

  predicate ResultSameCtx<V>(locals: set<string>, ctx: Context, res: Result<(V,Context)>)
  {
    match res
      case Success((_, ctx')) =>
        && ctx'.Keys == ctx.Keys
        // Rem.(SMH): I initially wrote this, but the proofs wouldn't go through
        // automatically: `ctx - locals == ctx' - locals`
        // Using forall quantifiers seems to work better in general, but in big
        // contexts it is usually a bad idea (unless we make definitions opaque).
        && forall x | x in ctx.Keys && x !in locals :: ctx'[x] == ctx[x]
      case Failure =>
        true
  }

  predicate ResultSameState<V>(st: S, res: Result<(V,Context)>)
  {
    ResultSameCtx(st.locals, st.ctx, res)
  }

  //
  // Below, we prove that if we evaluate an expression starting from equivalent contexts,
  // then we evaluate to equivalent results.
  //

  // Rem.: we need an optional variable, otherwise we can't prove ``InductBind_Fail``.
  // The reason is that if there is variable shadowing we ignore the body of the let,
  // but the induction hypothesis takes as precondition that `x` doesn't appear in the
  // expression: we thus have to update the state to reflect the fact that we don't need
  // this condition on the body.
  datatype MState = MState(locals: set<string>, ctx: Context)

  type S = MState
  type V = int
  type VS = seq<int>

  ghost const Zero: V := 0

  predicate Pre(st: S, e: Expr)
  {
    && IsPure(e, st.locals)
    && st.ctx.Keys >= st.locals
  }

  predicate PreEs(st: S, es: seq<Expr>)
  {
    && IsPure_Es(es, st.locals)
    && st.ctx.Keys >= st.locals
  }

  predicate P ...
  {
    var res := InterpExpr(e, st.ctx);
    Pre(st, e) ==> ResultSameState(st, res)
  }

  predicate P_Succ ...
  {
    var res := InterpExpr(e, st.ctx);
    && Pre(st, e)
    && ResultSameState(st, res)
    && res == Success((v, st'.ctx))
    && st'.locals == st.locals
  }

  predicate P_Fail ...
  {
    var res := InterpExpr(e, st.ctx);
    Pre(st, e) ==> res.Failure?
  }

  predicate Pes ...
  {
    var res := InterpExprs(es, st.ctx);
    PreEs(st, es) ==> ResultSameState(st, res)
  }

  predicate Pes_Succ ...
  {
    var res := InterpExprs(es, st.ctx);
    && PreEs(st, es)
    && ResultSameState(st, res)
    && res == Success((vs, st'.ctx))
    && st'.locals == st.locals
  }

  predicate Pes_Fail ...
  {
    var res := InterpExprs(es, st.ctx);
    PreEs(st, es) ==> res.Failure?
  }

  function AppendValue ...
  {
    [v] + vs
  }

  ghost const NilVS: VS := []

  function VS_Last ...
  {
    vs[|vs| - 1]
  }

  predicate UpdateState_Pre ...
  {
    && |vars| == |argvs|
  }

  function AssignState ...
  {
    var MState(x, ctx) := st;
    var bindings := VarsAndValuesToContext(vars, vals);
    var ctx1 := ctx + bindings;
    var st' := MState(x, ctx1);
    st'
  }

  function BindStartScope ...
  {
    var MState(locals, ctx) := st;
    var locals' := (set x | x in vars) + locals;
    var bindings := VarsAndValuesToContext(vars, vals);
    var ctx1 := ctx + bindings;
    var st' := MState(locals', ctx1);
    st'
  }

  function BindEndScope ...
  {
    var MState(x0, ctx0) := st0;
    var MState(x, ctx) := st;
    var ctx1 := ctx0 + (ctx - (set x | x in vars));
    var st' := MState(x0, ctx1);
    st'
  }

  function P_Step ...
  {
    var Success((v, ctx1)) := InterpExpr(e, st.ctx);
    (MState(st.locals, ctx1), v)
  }

  lemma P_Fail_Sound ... {}
  lemma P_Succ_Sound ... {}
  lemma InductVar ... {}
  lemma InductLiteral ... {}
  lemma InductIf_Fail ... {}
  lemma InductIf_Succ ... {}
  lemma InductOp_Fail ... {}
  lemma InductOp_Succ ... {}
  lemma InductSeq_Fail ... {}
  lemma InductSeq_Succ ... {}
  lemma InductAssign_Fail ... {}

  lemma InductAssign_Succ ... {}

  lemma InductBind_Fail ... {}
  lemma InductBind_Succ ... {}

  lemma InductExprs_Nil ... {}
  lemma InductExprs_Cons ... {}

  lemma InterpExpr_Pure(e: Expr, ctx: Context)
    requires IsPure(e)
    ensures
      match InterpExpr(e, ctx)
        case Success((_, ctx')) => ctx' == ctx
        case Failure => true
    // The final theorem.
  {
    P_Satisfied(MState({}, ctx), e);
  }
}
