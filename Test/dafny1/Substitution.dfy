// RUN: %dafny /compile:0 /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List = Nil | Cons(Expr, List)

datatype Expr =
  Const(int) |
  Var(int) |
  Nary(int, List)

ghost function Subst(e: Expr, v: int, val: int): Expr
{
  match e
  case Const(c) => e
  case Var(x) => if x == v then Expr.Const(val) else e
  case Nary(op, args) => Expr.Nary(op, SubstList(args, v, val))
}

ghost function SubstList(l: List, v: int, val: int): List
{
  match l
  case Nil => l
  case Cons(e, tail) => Cons(Subst(e, v, val), SubstList(tail, v, val))
}

lemma Theorem(e: Expr, v: int, val: int)
  ensures Subst(Subst(e, v, val), v, val) == Subst(e, v, val);
{
  match e {
    case Const(c) =>
    case Var(x) =>
    case Nary(op, args) =>
      Lemma(args, v, val);
  }
}

lemma Lemma(l: List, v: int, val: int)
  ensures SubstList(SubstList(l, v, val), v, val) == SubstList(l, v, val);
{
  match l {
    case Nil =>
    case Cons(e, tail) =>
      Theorem(e, v, val);
      Lemma(tail, v, val);
  }
}

// -------------------------------

datatype Expression =
  Const(int) |
  Var(int) |
  Nary(int, seq<Expression>)

ghost function Substitute(e: Expression, v: int, val: int): Expression
  decreases e;
{
  match e
  case Const(c) => e
  case Var(x) => if x == v then Expression.Const(val) else e
  case Nary(op, args) => Expression.Nary(op, SubstSeq(e, args, v, val))
}

ghost function SubstSeq(/*ghost*/ parent: Expression,
                         q: seq<Expression>, v: int, val: int): seq<Expression>
  requires (forall a :: a in q ==> a < parent);
  decreases parent, q;
{
  if q == [] then [] else
  SubstSeq(parent, q[..|q|-1], v, val) + [Substitute(q[|q|-1], v, val)]
}

lemma TheoremSeq(e: Expression, v: int, val: int)
  ensures Substitute(Substitute(e, v, val), v, val) == Substitute(e, v, val);
{
  match e {
    case Const(c) =>
    case Var(x) =>
    case Nary(op, args) =>
      ghost var seArgs := SubstSeq(e, args, v, val);
      LemmaSeq(e, args, v, val);

      ghost var se := Substitute(e, v, val);
      ghost var seArgs2 := SubstSeq(se, seArgs, v, val);
      LemmaSeq(se, seArgs, v, val);

      var N := |args|;
      var j := 0;
      while (j < N)
        invariant j <= N;
        invariant (forall k :: 0 <= k && k < j ==> seArgs2[k] == seArgs[k]);
      {
        TheoremSeq(args[j], v, val);
        j := j + 1;
      }
      assert seArgs == seArgs2;
  }
}

lemma LemmaSeq(parent: Expression, q: seq<Expression>, v: int, val: int)
  requires (forall a :: a in q ==> a < parent);
  ensures |SubstSeq(parent, q, v, val)| == |q|;
  ensures (forall k :: 0 <= k && k < |q| ==>
            SubstSeq(parent, q, v, val)[k] == Substitute(q[k], v, val));
{
  if (q == []) {
  } else {
    LemmaSeq(parent, q[..|q|-1], v, val);
  }
}
