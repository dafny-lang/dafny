datatype List {
  Nil;
  Cons(Expr, List);
}

datatype Expr {
  Const(int);
  Var(int);
  Nary(int, List);
}

static function Subst(e: Expr, v: int, val: int): Expr
  decreases e;
{
  match e
  case Const(c) => e
  case Var(x) => if x == v then #Expr.Const(val) else e
  case Nary(op, args) => #Expr.Nary(op, SubstList(args, v, val))
}

static function SubstList(l: List, v: int, val: int): List
  decreases l;
{
  match l
  case Nil => l
  case Cons(e, tail) => #List.Cons(Subst(e, v, val), SubstList(tail, v, val))
}

static ghost method Theorem(e: Expr, v: int, val: int)
  ensures Subst(Subst(e, v, val), v, val) == Subst(e, v, val);
  decreases e;
{
  match e {
    case Const(c) =>
    case Var(x) =>
    case Nary(op, args) =>
      call Lemma(args, v, val);
  }
}

static ghost method Lemma(l: List, v: int, val: int)
  ensures SubstList(SubstList(l, v, val), v, val) == SubstList(l, v, val);
  decreases l;
{
  match l {
    case Nil =>
    case Cons(e, tail) =>
      call Theorem(e, v, val);
      call Lemma(tail, v, val);
  }
}

// -------------------------------

datatype Expression {
  Const(int);
  Var(int);
  Nary(int, seq<Expression>);
}

static function Substitute(e: Expression, v: int, val: int): Expression
  decreases e, true;
{
  match e
  case Const(c) => e
  case Var(x) => if x == v then #Expression.Const(val) else e
  case Nary(op, args) => #Expression.Nary(op, SubstSeq(e, args, v, val))
}

static function SubstSeq(/*ghost*/ parent: Expression,
                         q: seq<Expression>, v: int, val: int): seq<Expression>
  requires (forall a :: a in q ==> a < parent);
  decreases parent, false, q;
{
  if q == [] then [] else
  SubstSeq(parent, q[..|q|-1], v, val) + [Substitute(q[|q|-1], v, val)]
}

static ghost method TheoremSeq(e: Expression, v: int, val: int)
  ensures Substitute(Substitute(e, v, val), v, val) == Substitute(e, v, val);
  decreases e, true;
{
  match e {
    case Const(c) =>
    case Var(x) =>
    case Nary(op, args) =>
      ghost var seArgs := SubstSeq(e, args, v, val);
      call LemmaSeq(e, args, v, val);

      ghost var se := Substitute(e, v, val);
      ghost var seArgs2 := SubstSeq(se, seArgs, v, val);
      call LemmaSeq(se, seArgs, v, val);

      var N := |args|;
      var j := 0;
      while (j < N)
        invariant j <= N;
        invariant (forall k :: 0 <= k && k < j ==> seArgs2[k] == seArgs[k]);
      {
        call TheoremSeq(args[j], v, val);
        j := j + 1;
      }
      assert seArgs == seArgs2;
  }
}

static ghost method LemmaSeq(ghost parent: Expression, ghost q: seq<Expression>,
                                    v: int, val: int)
  requires (forall a :: a in q ==> a < parent);
  ensures |SubstSeq(parent, q, v, val)| == |q|;
  ensures (forall k :: 0 <= k && k < |q| ==>
            SubstSeq(parent, q, v, val)[k] == Substitute(q[k], v, val));
  decreases q;
{
  if (q == []) {
  } else {
    call LemmaSeq(parent, q[..|q|-1], v, val);
  }
}
