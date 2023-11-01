// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "Utils.dfy"
include "AST.dfy"
include "Interp.dfy"
include "Induction.dfy"

module Equiv refines Induction {
  // A trivial example of the induction principle - mostly a sanity check.

  import opened Interp

  // Introducing ghost predicates to make reasoning harder and mimick the "real" Dind
  // proofs.
  ghost predicate EqValue(x: int, y: int)
  {
    x == y
  }

  ghost predicate EqSeqValue(x: seq<int>, y: seq<int>)
  {
    && |x| == |y|
    && forall i | 0 <= i < |x| :: EqValue(x[i], y[i])
  }

  ghost predicate {:opaque} EqCtx(ctx: Context, ctx': Context)
  {
    && ctx.Keys == ctx'.Keys
    && forall x | x in ctx.Keys :: ctx[x] == ctx'[x]
  }

  ghost predicate EqResult(res: InterpResult, res': InterpResult)
  {
    match (res, res')
      case (Success((v, ctx)), Success((v', ctx'))) =>
        && EqValue(v, v')
        && EqCtx(ctx, ctx')
      case (Failure, _) =>
        true
      case _ =>
        false
  }

  ghost predicate EqResultSeq(res: InterpResultSeq, res': InterpResultSeq)
  {
    match (res, res')
      case (Success((vs, ctx)), Success((vs', ctx'))) =>
        && EqSeqValue(vs, vs')
        && EqCtx(ctx, ctx')
      case (Failure, _) =>
        true
      case _ =>
        false
  }

  //
  // Below, we prove that if we evaluate an expression starting from equivalent contexts,
  // then we evaluate to equivalent results.
  //

  datatype MState = MState(ctx: Context, ctx': Context)
  datatype MValue = MValue(v: int, v': int)
  datatype MSeqValue = MSeqValue(vs: seq<int>, vs': seq<int>)

  type S = MState
  type V = MValue
  type VS = vs:MSeqValue | |vs.vs| == |vs.vs'| witness MSeqValue([], [])

  ghost const Zero: V := MValue(0, 0)

  ghost predicate Inv(st: MState)
  {
    && EqCtx(st.ctx, st.ctx')
  }

  ghost predicate P ...
  {
    var res := InterpExpr(e, st.ctx);
    var res' := InterpExpr(e, st.ctx');
    Inv(st) ==>
    EqResult(res, res')
  }

  ghost predicate P_Succ ...
  {
    var res := InterpExpr(e, st.ctx);
    var res' := InterpExpr(e, st.ctx');
    && Inv(st)
    && EqResult(res, res')
    && res == Success((v.v, st'.ctx))
    && res' == Success((v.v', st'.ctx'))
  }

  ghost predicate P_Fail ...
  {
    Inv(st) ==> InterpExpr(e, st.ctx).Failure?
  }

  ghost predicate Pes ...
  {
    var res := InterpExprs(es, st.ctx);
    var res' := InterpExprs(es, st.ctx');
    Inv(st) ==>
    EqResultSeq(res, res')
  }

  ghost predicate Pes_Succ ...
  {
    var res := InterpExprs(es, st.ctx);
    var res' := InterpExprs(es, st.ctx');
    && Inv(st)
    && EqResultSeq(res, res')
    && res == Success((vs.vs, st'.ctx))
    && res' == Success((vs.vs', st'.ctx'))
  }

  ghost predicate Pes_Fail ...
  {
    Inv(st) ==> InterpExprs(es, st.ctx).Failure?
  }

  ghost function AppendValue ...
  {
    MSeqValue([v.v] + vs.vs, [v.v'] + vs.vs')
  }

  ghost const NilVS: VS := MSeqValue([], [])

  ghost function VS_Last ...
  {
    var v := vs.vs[|vs.vs| - 1];
    var v' := vs.vs'[|vs.vs| - 1];
    MValue(v, v')
  }

  ghost predicate UpdateState_Pre ...
  {
    && Inv(st)
    && |vars| == |argvs.vs| == |argvs.vs'|
    && EqSeqValue(argvs.vs, argvs.vs')
  }

  lemma VarsAndValuesToContext_Eq(vars: seq<string>, vs: seq<int>, vs': seq<int>)
    requires |vars| == |vs| == |vs'|
    requires EqSeqValue(vs, vs')
    ensures
      var bindings := VarsAndValuesToContext(vars, vs);
      var bindings' := VarsAndValuesToContext(vars, vs');
      EqCtx(bindings, bindings')
  {
    reveal EqCtx();

    if vars == [] {}
    else {
      VarsAndValuesToContext_Eq(vars[1..], vs[1..], vs'[1..]);
    }
  }

  ghost function AssignState ...
    ensures Inv(st')
  {
    var MState(ctx, ctx') := st;
    var bindings := VarsAndValuesToContext(vars, vals.vs);
    var bindings' := VarsAndValuesToContext(vars, vals.vs');
    var ctx1 := ctx + bindings;
    var ctx1' := ctx' + bindings';
    var st' := MState(ctx1, ctx1');

    assert Inv(st') by {
      VarsAndValuesToContext_Eq(vars, vals.vs, vals.vs');
      assert EqCtx(bindings, bindings');
      reveal EqCtx();
    }

    st'
  }

  ghost function BindStartScope ...
    ensures Inv(st')
  {
    AssignState(st, vars, vals)
  }

  ghost function BindEndScope ...
    ensures Inv(st0) && Inv(st) ==> Inv(st')
  {
    var MState(ctx0, ctx0') := st0;
    var MState(ctx, ctx') := st;
    var ctx1 := ctx0 + (ctx - (set x | x in vars));
    var ctx1' := ctx0' + (ctx' - (set x | x in vars));
    var st' := MState(ctx1, ctx1');

    var b := Inv(st0) && Inv(st);
    assert b ==> Inv(st') by {
      if b {
        reveal EqCtx();
      }
    }

    st'
  }

  ghost function P_Step ...
  {
    var Success((v, ctx1)) := InterpExpr(e, st.ctx);
    var Success((v', ctx1')) := InterpExpr(e, st.ctx');
    (MState(ctx1, ctx1'), MValue(v, v'))
  }

  ghost function Pes_Step ...
  {
    var Success((vs, ctx1)) := InterpExprs(es, st.ctx);
    var Success((vs', ctx1')) := InterpExprs(es, st.ctx');
    (MState(ctx1, ctx1'), MSeqValue(vs, vs'))
  }

  lemma P_Fail_Sound ... {}
  lemma P_Succ_Sound ... {}
  lemma InductVar ... { reveal EqCtx(); }
  lemma InductLiteral ... {}
  lemma InductIf_Fail ... {}
  lemma InductIf_Succ ... {}
  lemma InductOp_Fail ... {}
  lemma InductOp_Succ ... {}
  lemma InductSeq_Fail ... {}
  lemma InductSeq_Succ ... {}
  lemma InductAssign_Fail ... {}
  lemma InductAssign_Succ ... { reveal EqCtx(); }
  lemma InductBind_Fail ...  {}
  lemma InductBind_Succ ... { reveal EqCtx(); }
  lemma InductExprs_Nil ... {}
  lemma InductExprs_Cons ... {}
}
