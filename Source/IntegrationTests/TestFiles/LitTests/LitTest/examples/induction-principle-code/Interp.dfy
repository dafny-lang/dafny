// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "Utils.dfy"
include "AST.dfy"

module Interp {
  import opened Utils
  import opened AST

  type Context = map<string, int>

  type InterpResult = Result<(int, Context)>
  type InterpResultSeq = Result<(seq<int>, Context)>

  function InterpBinOp(op: BinOp, x: int, y: int): int
  {
    match op
      case Add => x + y
      case Sub => x - y
      case Mul => x * y
  }

  function InterpExpr(e: Expr, ctx: Context): Result<(int, Context)>
    decreases e, 1
  {
    match e {
      case Var(name) =>
        if name in ctx.Keys then Success((ctx[name], ctx)) else Failure

      case Literal(n) =>
        Success((n, ctx))

      case Bind(bvars, bvals, body) =>
        var (vs, ctx1) :- InterpExprs(bvals, ctx);
        var bindings := VarsAndValuesToContext(bvars, vs);
        var ctx2 := ctx1 + bindings;
        var (bodyv, ctx3) :- InterpExpr(body, ctx2);
        var ctx4 := ctx1 + (ctx3 - (set x | x in bvars));
        Success((bodyv, ctx4))

      case Assign(avars, avals) =>
        var (vs, ctx1) :- InterpExprs(avals, ctx);
        // We could check that `avars <= ctx1.Keys`, but if we do so the assignment we
        // do here is not the same as for ``Bind`` (and may fail) which is annoying
        // for the proofs.
        var bindings := VarsAndValuesToContext(avars, vs);
        Success((0, ctx1 + bindings))

      case If(cond, thn, els) =>
        var (condv, ctx_cond) :- InterpExpr(cond, ctx);
        if condv != 0 then
          InterpExpr(thn, ctx_cond)
        else
          InterpExpr(els, ctx_cond)

      case Op(op, e1, e2) =>
        var (v1, ctx1) :- InterpExpr(e1, ctx);
        var (v2, ctx2) :- InterpExpr(e2, ctx1);
        Success((InterpBinOp(op, v1, v2), ctx2))

      case Seq(es) =>
        var (vs, ctx1) :- InterpExprs(es, ctx);
        if vs == [] then Success((0, ctx1))
        else Success((vs[|vs|-1], ctx1))
    }
  }

  function InterpExprs(es: seq<Expr>, ctx: Context): (r:Result<(seq<int>, Context)>)
    ensures r.Success? ==> |r.value.0| == |es|
    decreases es, 0
  {
    if es == [] then Success(([], ctx))
    else
      var (v, ctx1) :- InterpExpr(es[0], ctx);
      var (vs, ctx2) :- InterpExprs(es[1..], ctx1);
      Success(([v] + vs, ctx2))
  }

  function VarsAndValuesToContext(vars: seq<string>, values: seq<int>): (ctx:Context)
    requires |vars| == |values|
    ensures ctx.Keys == set x | x in vars
  {
    if vars == [] then map []
    else
      map [vars[0] := values[0]] + VarsAndValuesToContext(vars[1..], values[1..])
  }
}
