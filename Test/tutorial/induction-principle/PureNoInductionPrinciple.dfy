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

  lemma InterpExpr_Pure_WithLocals(e: Expr, locals: set<string>, ctx: Context)
    requires Pure.IsPure_WithLocals(locals, e)
    requires ctx.Keys >= locals
    ensures ResultSameCtx(locals, ctx, InterpExpr(e, ctx))
    decreases e, 1
  {
    match e
      case Var(name) =>
      case Literal(n) =>

      case Bind(bvars, bvals, body) =>
        var res1 := InterpExprs(bvals, ctx); // Manual introduction

        InterpExprs_Pure_WithLocals(bvals, locals, ctx); // Recursive call

        if res1.Success? { // Manual introduction
          var (vs, ctx1) := res1.value; // Manual introduction
          var bindings := VarsAndValuesToContext(bvars, vs); // Manual introduction
          var ctx2 := ctx1 + bindings; // Manual introduction
          var locals' := (set x | x in bvars) + locals;

          // Below: pay attention to the arguments (`locals'`, `ctx2` for instance)!
          InterpExpr_Pure_WithLocals(body, locals', ctx2); // Recursive call
          
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
        InterpExprs_Pure_WithLocals(avals, locals, ctx); // Recursive call

      case If(cond, thn, els) =>
        var res1 := InterpExpr(cond, ctx); // Manual introduction
        InterpExpr_Pure_WithLocals(cond, locals, ctx); // Recursive call

        if res1.Success? { // Manual introduction
          var (condv, ctx1) := res1.value; // Manual introduction

          InterpExpr_Pure_WithLocals(thn, locals, ctx1); // Recursive call
          InterpExpr_Pure_WithLocals(els, locals, ctx1); // Recursive call
        }
        else {}

      case Op(op, oe1, oe2) =>
        var res1 := InterpExpr(oe1, ctx); // Manual introduction
        InterpExpr_Pure_WithLocals(oe1, locals, ctx); // Recursive call

        if res1.Success? {
          var (v1, ctx1) := res1.value;
          InterpExpr_Pure_WithLocals(oe2, locals, ctx1); // Recursive call
        }
        else {}

      case Seq(es) =>
        InterpExprs_Pure_WithLocals(es, locals, ctx); // Recursive call
  }

  lemma InterpExprs_Pure_WithLocals(es: seq<Expr>, locals: set<string>, ctx: Context)
    requires Pure.IsPure_Es_WithLocals(locals, es)
    requires ctx.Keys >= locals
    ensures ResultSameCtx(locals, ctx, InterpExprs(es, ctx))
    decreases es, 0
  {
    if es == [] {} // Manual test
    else {
      var res1 := InterpExpr(es[0], ctx); // Manual introduction
      InterpExpr_Pure_WithLocals(es[0], locals, ctx); // Recursive call
      
      if res1.Success? {
        var (v, ctx1) := res1.value; // Manual introduction

        InterpExprs_Pure_WithLocals(es[1..], locals, ctx1);
      }
      else {}
    }
  }

  lemma InterpExpr_Pure(e: Expr, ctx: Context)
    requires Pure.IsPure(e)
    ensures
      match InterpExpr(e, ctx)
        case Success((_, ctx')) => ctx' == ctx
        case Failure => true
    // The final theorem.
  {
    InterpExpr_Pure_WithLocals(e, {}, ctx);
  }
}
