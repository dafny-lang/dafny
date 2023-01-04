// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "Utils.dfy"
include "AST.dfy"
include "Interp.dfy"
include "Induction.dfy"

module VarUnchanged refines Induction {
  // We write a small analysis which checks if a variable appears in an assignment in
  // an expression (we take into account shadowing introduced by let-bindings), and prove
  // that if it is not the case, then evaluating the expression leaves the variable
  // unchanged.

  import opened Interp

  predicate method VarUnchanged(x: string, e: Expr)
    // Returns true if no assignments of `x` (not shadowed by a let-binding) appears
    // in `e`.
    decreases e
  {
    match e
      case Var(name) => false
      case Literal(n) => false

      case Bind(bvars, bvals, body) =>
        // The rhs doesn't update x
        (forall e:Expr_Raw | e in bvals :: VarUnchanged(x, e)) &&
        // If the binding doesn't shadow x, the body of the let-binding doesn't update x
        (x in bvars || VarUnchanged(x, body))
      case Assign(avars, avals) =>
        x !in avars && (forall e:Expr_Raw | e in avals :: VarUnchanged(x, e))
      case If(cond, thn, els) =>
        VarUnchanged(x, cond) && VarUnchanged(x, thn) && VarUnchanged(x, els)
      case Op(op, oe1, oe2) =>
        VarUnchanged(x, oe1) && VarUnchanged(x, oe2)
      case Seq(es) =>
        forall e:Expr_Raw | e in es :: VarUnchanged(x, e)
  }

  predicate ResultSameX(st: S, res: InterpResult)
  {
    match res
      case Success((v, ctx)) =>
        st.x.Some? ==>
        && st.x.value in ctx.Keys
        && st.ctx[st.x.value] == ctx[st.x.value]
      case Failure =>
        true
  }

  predicate ResultSeqSameX(st: S, res: InterpResultSeq)
  {
    match res
      case Success((_, ctx)) =>
        st.x.Some? ==>
        && st.x.value in ctx.Keys
        && st.ctx[st.x.value] == ctx[st.x.value]
      case Failure =>
        true
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
  datatype MState = MState(x: Option<string>, ctx: Context)
  
  type S = st:MState | st.x.Some? ==> st.x.value in st.ctx.Keys
    witness MState(None, map [])
  type V = int
  type VS = seq<int>

  ghost const Zero: V := 0

  predicate Pre(st: S, e: Expr)
  {
    st.x.Some? ==> VarUnchanged(st.x.value, e)
  }

  predicate PreEs(st: S, es: seq<Expr>)
  {
    forall e | e in es :: Pre(st, e)
  }

  predicate P ...
  {
    var res := InterpExpr(e, st.ctx);
    Pre(st, e) ==> ResultSameX(st, res)
  }

  predicate P_Succ ...
  {
    var res := InterpExpr(e, st.ctx);
    && Pre(st, e)
    && ResultSameX(st, res)
    && res == Success((v, st'.ctx))
    && st'.x == st.x
  }

  predicate P_Fail ...
  {
    var res := InterpExpr(e, st.ctx);
    Pre(st, e) ==> res.Failure?
  }

  predicate Pes ...
  {
    var res := InterpExprs(es, st.ctx);
    PreEs(st, es) ==> ResultSeqSameX(st, res)
  }

  predicate Pes_Succ ...
  {
    var res := InterpExprs(es, st.ctx);
    && PreEs(st, es)
    && ResultSeqSameX(st, res)
    && res == Success((vs, st'.ctx))
    && st'.x == st.x
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
    var MState(x, ctx) := st;
    var x' := if x.Some? && x.value in vars then None else x;
    var bindings := VarsAndValuesToContext(vars, vals);
    var ctx1 := ctx + bindings;
    var st' := MState(x', ctx1);
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
    (MState(st.x, ctx1), v)
  }

  function Pes_Step ...
  {
    var Success((vs, ctx1)) := InterpExprs(es, st.ctx);
    (MState(st.x, ctx1), vs)
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
  lemma InductExprs_Cons ...
  {
    // This helps the SMT solver
    assert forall e' :: e' in ([e] + es) <==> e' == e || e' in es;
  }
}

