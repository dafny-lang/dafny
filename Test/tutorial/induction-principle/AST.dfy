// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "Utils.dfy"

module AST {
  import opened Utils

  datatype BinOp =
    | Add
    | Sub
    | Mul
  
  datatype Expr_Raw =
    | Var(name: string)
    | Literal(n: int)
    | Bind(bvars: seq<string>, bvals: seq<Expr_Raw>, body: Expr_Raw)
    | Assign(avars: seq<string>, avals: seq<Expr_Raw>)
    | If(cond: Expr_Raw, thn: Expr_Raw, els: Expr_Raw)
    | Op(op: BinOp, oe1: Expr_Raw, oe2: Expr_Raw)
    | Seq(es: seq<Expr_Raw>)
  {
    function method Depth() : nat
    {
      1 + match this {
        case Var(_) =>
          0
        case Literal(lit) =>
          0
        case Bind(bvars, bvals, body) =>
          var m := MaxF(var f := (e: Expr_Raw) requires e in bvals => e.Depth(); f, bvals, 0);
          Max(m, body.Depth())
        case Assign(avars, avals) =>
          MaxF(var f := (e: Expr_Raw) requires e in avals => e.Depth(); f, avals, 0)
        case If(cond, thn, els) =>
          Max(cond.Depth(), Max(thn.Depth(), els.Depth()))
        case Op(op, e1, e2) =>
          Max(e1.Depth(), e2.Depth())
        case Seq(es: seq<Expr_Raw>) =>
          MaxF(var f := (e: Expr_Raw) requires e in es => e.Depth(); f, es, 0)
      }
    }

    static predicate method All(e: Expr_Raw, p: (Expr_Raw) -> bool)
    {
      p(e) &&
      (match e
         case Var(name) => true
         case Literal(n) => true
         case Bind(bvars, bvals, body) =>
          && (forall e | e in bvals :: e.All(e, p))
          && All(body, p)
         case Assign(avars, avals) =>
          && forall e | e in avals :: e.All(e, p)
         case If(cond, thn, els) =>
          All(cond, p) && All(thn, p) && All(els, p)
         case Op(op, oe1, oe2) =>
          All(oe1, p) && All(oe2, p)
         case Seq(es) =>
          && forall e | e in es :: e.All(e, p)
      )
    }

    static predicate method All_Es(es: seq<Expr_Raw>, p: (Expr_Raw) -> bool)
      // Rem.: we pay attention of not making ``All_Es`` and ``All`` mutually
      // recursive, otherwise it causes problems in the proofs.
    {
      forall e | e in es :: e.All(e, p)
    }

    static predicate WellFormed_Single(e: Expr_Raw)
    {
      match e
        case Var(name) => true
        case Literal(n) => true
        case Bind(bvars, bvals, body) => |bvars| == |bvals|
        case Assign(avars, avals) => |avars| == |avals|
        case If(cond, thn, els) => true
        case Op(op, oe1, oe2) => true
        case Seq(es) => true
    }

    predicate WellFormed()
    {
      All(this, WellFormed_Single)
    }
  }

  type Expr = e:Expr_Raw | e.WellFormed() witness Var("x")
}
