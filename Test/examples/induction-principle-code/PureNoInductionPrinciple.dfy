// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "Utils.dfy"
include "AST.dfy"
include "Interp.dfy"
include "Pure.dfy"

module PureNoInductionPrinciple {
  // This module does the same proof as ``IsPure``, but without using the induction
  // principle. We do this to allow comparing the two approaches.

  import opened Utils
  import opened AST
  import opened Interp
  import Pure

  predicate ResultSameCtx<V>(locals: set<string>, ctx: Context, res: Result<(V,Context)>)
  {
    Pure.ResultSameCtx(locals, ctx, res)
  }

  lemma InterpExpr_Pure(e: Expr, ctx: Context, locals: set<string> := {})
    requires Pure.IsPure(e, locals)
    requires ctx.Keys >= locals
    ensures ResultSameCtx(locals, ctx, InterpExpr(e, ctx))
    decreases e, 1
  {
    match e
      case Var(name) =>
      case Literal(n) =>

      case Bind(bvars, bvals, body) =>
        var res1 := InterpExprs(bvals, ctx); // Manual introduction

        InterpExprs_Pure(bvals, ctx, locals); // Recursive call

        if res1.Success? { // Manual introduction
          var (vs, ctx1) := res1.value; // Manual introduction
          var bindings := VarsAndValuesToContext(bvars, vs); // Manual introduction
          var ctx2 := ctx1 + bindings; // Manual introduction
          var locals' := (set x | x in bvars) + locals;

          // Below: pay attention to the arguments (`locals'`, `ctx2` for instance)!
          InterpExpr_Pure(body, ctx2, locals'); // Recursive call
          
          // When the proofs fail, we often need to introduce more values,
          // just so that we can stare at them and write assertions. For instance:
          // ```
          // var res2 := InterpExpr(body, ctx2);
          // if res2.Success? {
          //   var (bodyv, ctx3) := res2.value;
          //   ...
          // }
          // else {}
          // ```
        }
        else {}

      case Assign(avars, avals) =>
        InterpExprs_Pure(avals, ctx, locals); // Recursive call

      case If(cond, thn, els) =>
        var res1 := InterpExpr(cond, ctx); // Manual introduction
        InterpExpr_Pure(cond, ctx, locals); // Recursive call

        if res1.Success? { // Manual introduction
          var (condv, ctx1) := res1.value; // Manual introduction

          InterpExpr_Pure(thn, ctx1, locals); // Recursive call
          InterpExpr_Pure(els, ctx1, locals); // Recursive call
        }
        else {}

      case Op(op, oe1, oe2) =>
        var res1 := InterpExpr(oe1, ctx); // Manual introduction
        InterpExpr_Pure(oe1, ctx, locals); // Recursive call

        if res1.Success? {
          var (v1, ctx1) := res1.value;
          InterpExpr_Pure(oe2, ctx1, locals); // Recursive call
        }
        else {}

      case Seq(es) =>
        InterpExprs_Pure(es, ctx, locals); // Recursive call
  }

  lemma InterpExprs_Pure(es: seq<Expr>, ctx: Context, locals: set<string> := {})
    requires Pure.IsPure_Es(es, locals)
    requires ctx.Keys >= locals
    ensures ResultSameCtx(locals, ctx, InterpExprs(es, ctx))
    decreases es, 0
  {
    if es == [] {} // Manual test
    else {
      var res1 := InterpExpr(es[0], ctx); // Manual introduction
      InterpExpr_Pure(es[0], ctx, locals); // Recursive call
      
      if res1.Success? {
        var (v, ctx1) := res1.value; // Manual introduction

        InterpExprs_Pure(es[1..], ctx1, locals);
      }
      else {}
    }
  }
}
