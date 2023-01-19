// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "Utils.dfy"
include "AST.dfy"
include "Interp.dfy"

abstract module Induction {
  import opened Utils
  import opened AST

  // A state
  type S(!new)

  // A value
  type V(!new)

  // A sequence of values
  type VS(!new)

  ghost const Zero: V

  // ``P`` is the property of interest that we want to prove about the interpreter. It is often
  // possible to distinguish two cases in the proof: the case corresponding to a successful
  // execution of the interpreter, and the case corresponding to a failing execution. For instance,
  // let's say you want to prove that evaluating a pure expression leaves the state unchanged:
  // the property is trivially true in case the interpreter fails its execution. For this reason,
  // we decompose ``P`` into ``P_Fail`` (failed execution) and ``P_Succ`` (successful execution,
  // which also takes as inputs the state and value resulting from the execution).
  //
  // One important property to enforce is that:
  // `P(st, e) <==> P_Fail(st, e) || exists st', v :: P_Succ(st, e, st', v)`
  // This is enforced by: ``P_Fail_Sound``, ``P_Succ_Sound`` and ``P_Step``.
  predicate P(st: S, e: Expr)
  predicate P_Succ(st: S, e: Expr, st': S, v: V) // Success
  predicate P_Fail(st: S, e: Expr) // Failure

  // ``Pes`` is the property of interest over sequences of expressions.
  predicate Pes(st: S, es: seq<Expr>)
  predicate Pes_Succ(st: S, es: seq<Expr>, st': S, vs: VS) // Success
  predicate Pes_Fail(st: S, es: seq<Expr>) // Failure

  function AppendValue(v: V, vs: VS): VS // Returns: [v] + vs

  // Empty sequence of values
  ghost const NilVS: VS

  function VS_Last(vs: VS): V
    requires vs != NilVS

  predicate UpdateState_Pre(st: S, vars: seq<string>, argvs: VS)

  // For the ``Assign`` case
  function AssignState(st: S, vars: seq<string>, vals: VS): (st':S)
    requires UpdateState_Pre(st, vars, vals)

  // For the ``Bind`` case
  function BindStartScope(st: S, vars: seq<string>, vals: VS): (st':S)
    requires UpdateState_Pre(st, vars, vals)

  // For ``Bind``: used to remove from the context the variables introduced by the bind, while
  // preserving the mutation. `st0` is the state just before we introduce the let-bounded variables,
  // `st1 is the state resulting from evaluating the body.
  function BindEndScope(st0: S, st: S, vars: seq<string>): (st':S)

  function P_Step(st: S, e: Expr): (res: (S, V))
    requires P(st, e)
    requires !P_Fail(st, e)
    ensures P_Succ(st, e, res.0, res.1)

  function Pes_Step(st: S, es: seq<Expr>): (res: (S, VS))
    requires Pes(st, es)
    requires !Pes_Fail(st, es)
    ensures Pes_Succ(st, es, res.0, res.1)

  lemma P_Fail_Sound(st: S, e: Expr)
    requires P_Fail(st, e)
    ensures P(st, e)

  lemma P_Succ_Sound(st: S, e: Expr, st': S, v: V)
    requires P_Succ(st, e, st', v)
    ensures P(st, e)

  lemma Pes_Fail_Sound(st: S, es: seq<Expr>)
    requires Pes_Fail(st, es)
    ensures Pes(st, es)

  lemma Pes_Succ_Sound(st: S, es: seq<Expr>, st': S, vs: VS)
    requires Pes_Succ(st, es, st', vs)
    ensures Pes(st, es)

  lemma InductVar(st: S, e: Expr)
    requires e.Var?
    requires !P_Fail(st, e)
    ensures P(st, e)

  lemma InductLiteral(st: S, e: Expr)
    requires e.Literal?
    requires !P_Fail(st, e)
    ensures P(st, e)

  lemma InductIf_Fail(st: S, e: Expr, cond: Expr, thn: Expr, els: Expr)
    requires e.If? && e.cond == cond && e.thn == thn && e.els == els
    requires !P_Fail(st, e)
    requires P(st, cond)
    ensures !P_Fail(st, cond)

  lemma InductIf_Succ(st: S, e: Expr, cond: Expr, thn: Expr, els: Expr, st_cond: S, condv: V)
    requires e.If? && e.cond == cond && e.thn == thn && e.els == els
    requires !P_Fail(st, e)
    requires P_Succ(st, cond, st_cond, condv)
    requires P(st_cond, thn)
    requires P(st_cond, els)
    ensures P(st, e)

  lemma InductOp_Fail(st: S, e: Expr, op: BinOp, e1: Expr, e2: Expr)
    requires e.Op? && e.op == op && e.oe1 == e1 && e.oe2 == e2
    requires !P_Fail(st, e)
    ensures !P_Fail(st, e1)
    ensures forall st1, v1 | P_Succ(st, e1, st1, v1) :: !P_Fail(st1, e2)

  lemma InductOp_Succ(st: S, e: Expr, op: BinOp, e1: Expr, e2: Expr, st1: S, v1: V)
    requires e.Op? && e.op == op && e.oe1 == e1 && e.oe2 == e2
    requires !P_Fail(st, e)
    requires P_Succ(st, e1, st1, v1)
    requires P(st1, e2)
    ensures P(st, e)

  lemma InductSeq_Fail(st: S, e: Expr, es: seq<Expr>)
    requires e.Seq? && e.es == es
    requires !P_Fail(st, e)
    ensures !Pes_Fail(st, es)

  lemma InductSeq_Succ(st: S, e: Expr, es: seq<Expr>, st1: S, vs: VS)
    requires e.Seq? && e.es == es
    requires !P_Fail(st, e)
    requires Pes_Succ(st, es, st1, vs)
    ensures P(st, e)

  lemma InductAssign_Fail(st: S, e: Expr, avars: seq<string>, avals: seq<Expr>)
    requires e.Assign? && e.avars == avars && e.avals == avals
    requires !P_Fail(st, e)
    requires Pes(st, avals)
    ensures !Pes_Fail(st, avals)
    ensures forall st1, vs | Pes_Succ(st, avals, st1, vs) :: UpdateState_Pre(st1, avars, vs)

  lemma InductAssign_Succ(
    st: S, e: Expr, avars: seq<string>, avals: seq<Expr>, st1: S, vs: VS, st2: S)
    requires e.Assign? && e.avars == avars && e.avals == avals
    requires !P_Fail(st, e)
    requires Pes_Succ(st, avals, st1, vs)
    requires UpdateState_Pre(st1, avars, vs)
    requires st2 == AssignState(st1, avars, vs)
    // This post is not necessary: what matters is that ``AssignState`` appears somewhere,
    // but it may help Z3.
    ensures P_Succ(st, e, st2, Zero)
    ensures P(st, e)

  lemma InductBind_Fail(st: S, e: Expr, bvars: seq<string>, bvals: seq<Expr>, body: Expr)
    requires e.Bind? && e.bvars == bvars && e.bvals == bvals && e.body == body
    requires !P_Fail(st, e)
    requires Pes(st, bvals)
    ensures !Pes_Fail(st, bvals)
    ensures
      forall st1, vs | Pes_Succ(st, bvals, st1, vs) ::
      && UpdateState_Pre(st1, bvars, vs)
      && !P_Fail(BindStartScope(st1, bvars, vs), body)

  lemma InductBind_Succ(
    st: S, e: Expr, bvars: seq<string>, bvals: seq<Expr>, body: Expr,
    st1: S, bvarvs: VS, st2: S, st3: S, v: V, st4: S)
    requires e.Bind? && e.bvars == bvars && e.bvals == bvals && e.body == body
    requires !P_Fail(st, e)
    requires Pes_Succ(st, bvals, st1, bvarvs)
    requires UpdateState_Pre(st1, bvars, bvarvs)
    requires st2 == BindStartScope(st1, bvars, bvarvs)
    requires P_Succ(st2, body, st3, v)
    requires st4 == BindEndScope(st1, st3, bvars) // ``StateBindEndScope`` may have a postcondition, so it's good to have it
    ensures P_Succ(st, e, st4, v)

  lemma InductExprs_Nil(st: S)
    ensures !Pes_Fail(st, []) ==> Pes_Succ(st, [], st, NilVS)

  lemma InductExprs_Cons(st: S, e: Expr, es: seq<Expr>)
    ensures P_Fail(st, e) ==> Pes_Fail(st, [e] + es)
    ensures !P_Fail(st, e) ==> forall st1, v :: P_Succ(st, e, st1, v) && Pes_Fail(st1, es) ==> Pes_Fail(st, [e] + es)
    ensures forall st1, v, st2, vs :: P_Succ(st, e, st1, v) && Pes_Succ(st1, es, st2, vs) ==> Pes_Succ(st, [e] + es, st2, AppendValue(v, vs))

  //
  // Lemmas
  //

  lemma P_Satisfied(st: S, e: Expr)
    ensures P(st, e)
    decreases e, 3
  {
    if P_Fail(st, e) {
      P_Fail_Sound(st, e);
    }
    else {
      P_Satisfied_Succ(st, e);
    }
  }

  lemma P_Satisfied_Succ(st: S, e: Expr)
    requires !P_Fail(st, e)
    ensures P(st, e)
    decreases e, 2
  {
    match e {
      case Var(_) =>
        InductVar(st, e);

      case Literal(_) =>
        InductLiteral(st, e);

      case Op(op, e1, e2) =>
        // Recursion
        P_Satisfied(st, e1);

        assert !P_Fail(st, e1) by { InductOp_Fail(st, e, op, e1, e2); }
        var (st1, v1) := P_Step(st, e1);

        // Recursion
        P_Satisfied(st1, e2);

        assert !P_Fail(st1, e2) by { InductOp_Fail(st, e, op, e1, e2); }
        var (st2, v2) := P_Step(st1, e2);

        InductOp_Succ(st, e, op, e1, e2, st1, v1);

      case Seq(es) =>
        // Recursion
        Pes_Satisfied(st, es);

        assert !Pes_Fail(st, es) by { InductSeq_Fail(st, e, es); }
        var (st1, vs) := Pes_Step(st, es);
        
        InductSeq_Succ(st, e, es, st1, vs);

      case If(cond, thn, els) =>
        // Recursion
        P_Satisfied(st, cond);

        // Evaluate the condition
        InductIf_Fail(st, e, cond, thn, els);
        assert !P_Fail(st, cond);
        var (st_cond, condv) := P_Step(st, cond);

        P_Satisfied(st_cond, thn); // Recursion
        P_Satisfied(st_cond, els); // Recursion

        InductIf_Succ(st, e, cond, thn, els, st_cond, condv);

      case Assign(avars, avals) =>
        // Recursion
        Pes_Satisfied(st, avals);

        assert !Pes_Fail(st, avals) by { InductAssign_Fail(st, e, avars, avals); }
        var (st1, vs) := Pes_Step(st, avals);

        assert UpdateState_Pre(st1, avars, vs) by { InductAssign_Fail(st, e, avars, avals); }
        var st2 := AssignState(st1, avars, vs);
        InductAssign_Succ(st, e, avars, avals, st1, vs, st2);

      case Bind(bvars, bvals, body) =>
        Pes_Satisfied(st, bvals); // Recursion
        assert !Pes_Fail(st, bvals) by { InductBind_Fail(st, e, bvars, bvals, body); }
        var (st1, bvarvs) := Pes_Step(st, bvals);

        assert UpdateState_Pre(st1, bvars, bvarvs) by { InductBind_Fail(st, e, bvars, bvals, body); }
        var st2 := BindStartScope(st1, bvars, bvarvs);
        P_Satisfied(st2, body); // Recursion
        assert !P_Fail(st2, body) by { InductBind_Fail(st, e, bvars, bvals, body); }

        var (st3, v) := P_Step(st2, body);
        var st4 := BindEndScope(st1, st3, bvars);

        InductBind_Succ(st, e, bvars, bvals, body, st1, bvarvs, st2, st3, v, st4);
        P_Succ_Sound(st, e, st4, v);
    }
  }

  lemma Pes_Satisfied(st: S, es: seq<Expr>)
    ensures Pes(st, es)
    decreases es, 1
  {
    if Pes_Fail(st, es) {
      Pes_Fail_Sound(st, es);
    }
    else {
      Pes_Satisfied_Succ(st, es);
    }
  }

  lemma Pes_Satisfied_Succ(st: S, es: seq<Expr>)
    requires !Pes_Fail(st, es)
    ensures Pes(st, es)
    decreases es, 0
  {
    if es == [] {
      InductExprs_Nil(st);
      assert Pes_Succ(st, [], st, NilVS);
      Pes_Succ_Sound(st, [], st, NilVS);
    }
    else {
      var e := es[0];
      var es' := es[1..];
      assert [e] + es' == es;

      P_Satisfied(st, e); // Recursion

      if P_Fail(st, e) {
        InductExprs_Cons(st, e, es');
        assert Pes_Fail(st, [e] + es');
        Pes_Fail_Sound(st, [e] + es');
      }
      else {
        var (st1, v) := P_Step(st, e);
        Pes_Satisfied(st1, es'); // Recursion

        if Pes_Fail(st1, es') {
          InductExprs_Cons(st, e, es');
          assert Pes_Fail(st, [e] + es');
          Pes_Fail_Sound(st, [e] + es');
        }
        else {
          var (st2, vs) := Pes_Step(st1, es');
          InductExprs_Cons(st, e, es');
          assert Pes_Succ(st, [e] + es', st2, AppendValue(v, vs));
          Pes_Succ_Sound(st, [e] + es', st2, AppendValue(v, vs));
        }
      }
    }
  }
}
