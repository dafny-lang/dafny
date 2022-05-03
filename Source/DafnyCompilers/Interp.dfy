include "CompilerCommon.dfy"
include "Library.dfy"
include "Values.dfy"

module Interp {
  import opened Lib.Datatypes
  import opened DafnyCompilerCommon.AST
  import opened DafnyCompilerCommon.Predicates
  import V = Values

  predicate method Pure1(e: Expr) {
    match e {
      case Literal(lit) => true
      case Apply(Lazy(op), args: seq<Expr>) =>
        true
      case Apply(Eager(op), args: seq<Expr>) =>
        match op {
          case UnaryOp(uop: UnaryOp.Op) => true
          case BinaryOp(bop: BinaryOp) => true
          case DataConstructor(name: Path, typeArgs: seq<Type.Type>) => true
          case Builtin(Display(_)) => true
          case Builtin(Print) => false
          case MethodCall(classType, receiver, typeArgs) => false
          case FunctionCall() => true
        }
      case Block(stmts: seq<Expr>) => true
      case If(cond: Expr, thn: Expr, els: Expr) => true
      case Unsupported(_) => false
    }
  }

  predicate method Pure(e: Expr) {
    Predicates.Deep.All_Expr(e, Pure1)
  }

  predicate method SupportsInterp1(e: Expr) {
    AST.Exprs.WellFormed(e) &&
    var FALSE := false;
    match e {
      case Literal(lit) => true
      case Apply(Lazy(op), args: seq<Expr>) =>
        true
      case Apply(Eager(op), args: seq<Expr>) =>
        match op {
          case UnaryOp(uop: UnaryOp.Op) => FALSE
          case BinaryOp(bop: BinaryOp) => true
          case DataConstructor(name: Path, typeArgs: seq<Type.Type>) => FALSE
          case Builtin(Display(_)) => FALSE
          case Builtin(Print) => false
          case MethodCall(classType, receiver, typeArgs) => false
          case FunctionCall() => FALSE
        }
      case Block(stmts: seq<Expr>) => false
      case If(cond: Expr, thn: Expr, els: Expr) => true
      case Unsupported(_) => false
    }
  }

  predicate method SupportsInterp(e: Expr) {
    Predicates.Deep.All_Expr(e, SupportsInterp1)
  }

  lemma SupportsInterp_Pure(e: Expr)
    requires SupportsInterp1(e)
    ensures Pure1(e)
  {

  }

  function method InterpLiteral(a: AST.Exprs.Literal) : V.T {
    match a
      case LitBool(b: bool) => V.Bool(b)
      case LitInt(i: int) => V.Int(i)
      case LitReal(r: real) => V.Real(r)
      case LitChar(c: char) => V.Char(c)
      case LitString(s: string, verbatim: bool) =>
        V.Seq(seq(|s|, i requires 0 <= i < |s| => V.Char(s[i])))
  }

  type Context = map<string, V.T>

  datatype InterpError =
    | TypeError(e: Expr, value: V.T, expected: Type) // TODO rule out type errors through Wf predicate?
    | InvalidExpression(e: Expr) // TODO rule out in Wf predicate?
    | Unsupported(e: Expr) // TODO rule out in SupportsInterp predicate
    | Overflow(x: int, low: int, high: int)
    | DivisionByZero

  datatype InterpSuccess<A> =
    | OK(v: A, ctx: Context)

  type InterpResult<A> =
    Result<InterpSuccess<A>, InterpError>

  type PureInterpResult<A> =
    Result<A, InterpError>

  function method LiftPureResult<A>(ctx: Context, r: PureInterpResult<A>)
    : InterpResult<A>
  {
    var v :- r;
    Success(OK(v, ctx))
  }

  function method InterpExpr(e: Expr, ctx: Context := map[]) : InterpResult<V.T>
    requires SupportsInterp(e)
    decreases e, 1
  {
    Predicates.Deep.AllImpliesChildren(e, SupportsInterp1);
    match e {
      case Literal(lit) => Success(OK(InterpLiteral(lit), ctx))
      case Apply(Lazy(op), args: seq<Expr>) =>
        InterpLazy(e, ctx)
      case Apply(Eager(op), args: seq<Expr>) =>
        var OK(argsv, ctx) :- InterpExprs(args, ctx);
        match op {
          case BinaryOp(bop: BinaryOp) =>
            assert |argsv| == 2;
            LiftPureResult(ctx, InterpBinaryOp(e, bop, argsv[0], argsv[1]))
        }
      case If(cond, thn, els) =>
        var OK(condv, ctx) :- InterpExprWithType(cond, Type.Bool, ctx);
        if condv.b then InterpExpr(thn, ctx) else InterpExpr(els, ctx)
    }
  }

  function method InterpExprWithType(e: Expr, ty: Type, ctx: Context := map[])
    : (r: InterpResult<V.T>)
    requires SupportsInterp(e)
    decreases e, 2
    ensures r.Success? ==> r.value.v.HasType(ty)
  {
    var OK(val, ctx) :- InterpExpr(e, ctx);
    :- Need(val.HasType(ty), TypeError(e, val, ty));
    Success(OK(val, ctx))
  }

  function method InterpExprs(es: seq<Expr>, ctx: Context)
    : (r: InterpResult<seq<V.T>>)
    requires forall e | e in es :: SupportsInterp(e)
    ensures r.Success? ==> |r.value.v| == |es|
  {
    if es == [] then Success(OK([], ctx))
    else
      var OK(v, ctx) :- InterpExpr(es[0], ctx);
      var OK(vs, ctx) :- InterpExprs(es[1..], ctx);
      Success(OK([v] + vs, ctx))
  }

  function method InterpLazy(e: Expr, ctx: Context)
    : InterpResult<V.T>
    requires e.Apply? && e.aop.Lazy? && SupportsInterp(e)
    decreases e, 0
  {
    // DISCUSS: An alternative implementation would be to evaluate but discard
    // the second context if a short-circuit happens.
    Predicates.Deep.AllImpliesChildren(e, SupportsInterp1);
    var op, e0, e1 := e.aop.lOp, e.args[0], e.args[1];
    var OK(v0, ctx0) :- InterpExprWithType(e0, Type.Bool, ctx);
    match (op, v0)
      case (And, Bool(false)) => Success(OK(V.Bool(false), ctx0))
      case (Or,  Bool(true))  => Success(OK(V.Bool(true), ctx0))
      case (Imp, Bool(false)) => Success(OK(V.Bool(true), ctx0))
      case (_,   Bool(b)) =>
        assert op in {Exprs.And, Exprs.Or, Exprs.Imp};
        InterpExprWithType(e1, Type.Bool, ctx0)
  }

  // Alternate implementation of ``InterpLazy``; less efficient, but more
  // closely matches intuition.
  function method InterpLazy_Eagerly(e: Expr, ctx: Context)
    : InterpResult<V.T>
    requires e.Apply? && e.aop.Lazy? && SupportsInterp(e)
    decreases e, 0
  {
    Predicates.Deep.AllImpliesChildren(e, SupportsInterp1);
    var op, e0, e1 := e.aop.lOp, e.args[0], e.args[1];
    var OK(v0, ctx0) :- InterpExprWithType(e0, Type.Bool, ctx);
    var OK(v1, ctx1) :- InterpExprWithType(e1, Type.Bool, ctx0);
    match (op, v0, v1)
      case (And, Bool(b0), Bool(b1)) => Success(OK(V.Bool(b0 && b1), if b0 then ctx1 else ctx0))
      case (Or,  Bool(b0), Bool(b1)) => Success(OK(V.Bool(b0 || b1), if b0 then ctx0 else ctx1))
      case (Imp, Bool(b0), Bool(b1)) => Success(OK(V.Bool(b0 ==> b1), if b0 then ctx1 else ctx0))
  }

  lemma InterpLazy_Complete(e: Expr, ctx: Context)
    requires e.Apply? && e.aop.Lazy? && SupportsInterp(e)
    requires InterpLazy(e, ctx).Failure?
    ensures InterpLazy_Eagerly(e, ctx) == InterpLazy(e, ctx)
  {}

  lemma InterpLazy_Eagerly_Sound(e: Expr, ctx: Context)
    requires e.Apply? && e.aop.Lazy? && SupportsInterp(e)
    requires InterpLazy_Eagerly(e, ctx).Success?
    ensures InterpLazy_Eagerly(e, ctx) == InterpLazy(e, ctx)
  {}

  function method InterpBinaryOp(expr: Expr, bop: AST.BinaryOp, v0: V.T, v1: V.T)
    : PureInterpResult<V.T>
  {
    match bop
      case Numeric(op) => InterpNumeric(expr, op, v0, v1)
      case Logical(op) => InterpLogical(expr, op, v0, v1)
      case Eq(op) => match op { // FIXME which types is this Eq applicable to (vs. the type-specific ones?)
        case EqCommon() => Success(V.Bool(v0 == v1))
        case NeqCommon() => Success(V.Bool(v0 != v1))
      }
      case BV(op) => Failure(Unsupported(expr))
      case Char(op) => InterpChar(expr, op, v0, v1)
      case Sets(op) => InterpSets(expr, op, v0, v1)
      case MultiSets(op) => InterpMultiSets(expr, op, v0, v1)
      case Sequences(op) => InterpSequences(expr, op, v0, v1)
      case Maps(op) => InterpMaps(expr, op, v0, v1)
      case Datatypes(op) => Failure(Unsupported(expr))

  }

  function method InterpNumeric(expr: Expr, op: BinaryOps.Numeric, v0: V.T, v1: V.T)
    : PureInterpResult<V.T>
  {
    match (v0, v1) {
      // Separate functions to more easily check exhaustiveness
      case (Int(x1), Int(x2)) => InterpInt(expr, op, x1, x2)
      case (Char(x1), Char(x2)) => InterpNumericChar(expr, op, x1, x2)
      case (Real(x1), Real(x2)) => InterpReal(expr, op, x1, x2)
      case _ => Failure(InvalidExpression(expr)) // FIXME: Wf
    }
  }

  function method CheckDivisionByZero(b: bool) : Outcome<InterpError> {
    if b then Fail(DivisionByZero) else Pass
  }

  function method InterpInt(expr: Expr, bop: AST.BinaryOps.Numeric, x1: int, x2: int)
    : PureInterpResult<V.T>
  {
    match bop {
      case Lt() => Success(V.Bool(x1 < x2))
      case Le() => Success(V.Bool(x1 <= x2))
      case Ge() => Success(V.Bool(x1 >= x2))
      case Gt() => Success(V.Bool(x1 > x2))
      case Add() => Success(V.Int(x1 + x2))
      case Sub() => Success(V.Int(x1 - x2))
      case Mul() => Success(V.Int(x1 * x2))
      case Div() => :- CheckDivisionByZero(x2 == 0); Success(V.Int(x1 / x2))
      case Mod() => :- CheckDivisionByZero(x2 == 0); Success(V.Int(x1 % x2))
    }
  }

  function method CheckOverflow(x: int, low: int, high: int) : PureInterpResult<int> {
    if low <= x < high then Success(x) else Failure(Overflow(x, low, high))
  }

  function method InterpNumericChar(expr: Expr, bop: AST.BinaryOps.Numeric, x1: char, x2: char)
    : PureInterpResult<V.T>
  {
    match bop { // FIXME: These first four cases are not used (see InterpChar instead)
      case Lt() => Success(V.Bool(x1 < x2))
      case Le() => Success(V.Bool(x1 <= x2))
      case Ge() => Success(V.Bool(x1 >= x2))
      case Gt() => Success(V.Bool(x1 > x2))
      case Add() => var x :- CheckOverflow(x1 as int + x2 as int, 0, 256); Success(V.Char(x as char))
      case Sub() => var x :- CheckOverflow(x1 as int - x2 as int, 0, 256); Success(V.Char(x as char))
      case Mul() => Failure(Unsupported(expr))
      case Div() => Failure(Unsupported(expr))
      case Mod() => Failure(Unsupported(expr))
    }
  }

  function method InterpReal(expr: Expr, bop: AST.BinaryOps.Numeric, x1: real, x2: real)
    : PureInterpResult<V.T>
  {
    match bop {
      case Lt() => Success(V.Bool(x1 < x2))
      case Le() => Success(V.Bool(x1 <= x2))
      case Ge() => Success(V.Bool(x1 >= x2))
      case Gt() => Success(V.Bool(x1 > x2))
      case Add() => Success(V.Real(x1 + x2))
      case Sub() => Success(V.Real(x1 - x2))
      case Mul() => Success(V.Real(x1 * x2))
      case Div() => :- CheckDivisionByZero(x2 == 0 as real); Success(V.Real(x1 / x2))
      case Mod() => Failure(Unsupported(expr))
    }
  }

  function method InterpLogical(expr: Expr, op: BinaryOps.Logical, v0: V.T, v1: V.T)
    : PureInterpResult<V.T>
  {
    match (v0, v1) {
      case (Bool(b1), Bool(b2)) =>
        match op {
          case Iff() => Success(V.Bool(b1 <==> b2))
        }
      case _ => Failure(InvalidExpression(expr)) // FIXME: Wf
    }
  }

  function method InterpChar(expr: Expr, op: AST.BinaryOps.Char, v0: V.T, v1: V.T)
    : PureInterpResult<V.T>
  { // FIXME eliminate distinction between GtChar and GT?
    match (v0, v1) {
      case (Char(x1), Char(x2)) =>
        match op {
          case LtChar() => Success(V.Bool(x1 < x2))
          case LeChar() => Success(V.Bool(x1 <= x2))
          case GeChar() => Success(V.Bool(x1 >= x2))
          case GtChar() => Success(V.Bool(x1 > x2))
        }
      case _ => Failure(InvalidExpression(expr)) // FIXME: Wf
    }
  }

  function method InterpSets(expr: Expr, op: BinaryOps.Sets, v0: V.T, v1: V.T)
    : PureInterpResult<V.T>
  {
    match (v0, v1)
      case (Set(s0), Set(s1)) =>
        match op {
          case SetEq() => Success(V.Bool(s0 == s1))
          case SetNeq() => Success(V.Bool(s0 != s1))
          case Subset() => Success(V.Bool(s0 <= s1))
          case Superset() => Success(V.Bool(s0 >= s1))
          case ProperSubset() => Success(V.Bool(s0 < s1))
          case ProperSuperset() => Success(V.Bool(s0 > s1))
          case Disjoint() => Success(V.Bool(s0 !! s1))
          case Union() => Success(V.Set(s0 + s1))
          case Intersection() => Success(V.Set(s0 * s1))
          case SetDifference() => Success(V.Set(s0 - s1))
          case InSet() => Failure(InvalidExpression(expr))
          case NotInSet() => Failure(InvalidExpression(expr))
        }
      case (_, Set(s1)) =>
        match op {
          case InSet() => Success(V.Bool(v0 in s1))
          case NotInSet() => Success(V.Bool(v0 !in s1))
          case _ => Failure(InvalidExpression(expr))
        }
      case _ => Failure(InvalidExpression(expr))
  }

  function method InterpMultiSets(expr: Expr, op: BinaryOps.MultiSets, v0: V.T, v1: V.T)
    : PureInterpResult<V.T>
  {
    match (v0, v1)
      case (MultiSet(m0), MultiSet(m1)) =>
        match op {
          case MultiSetEq() => Success(V.Bool(m0 == m1))
          case MultiSetNeq() => Success(V.Bool(m0 != m1))
          case MultiSubset() => Success(V.Bool(m0 <= m1))
          case MultiSuperset() => Success(V.Bool(m0 >= m1))
          case ProperMultiSubset() => Success(V.Bool(m0 < m1))
          case ProperMultiSuperset() => Success(V.Bool(m0 > m1))
          case MultiSetDisjoint() => Success(V.Bool(m0 !! m1))
          case MultiSetUnion() => Success(V.MultiSet(m0 + m1))
          case MultiSetIntersection() => Success(V.MultiSet(m0 * m1))
          case MultiSetDifference() => Success(V.MultiSet(m0 - m1))
          case InMultiSet() => Failure(InvalidExpression(expr))
          case NotInMultiSet() => Failure(InvalidExpression(expr))
        }
      case (_, MultiSet(s1)) =>
        match op {
          case InMultiSet() => Success(V.Bool(v0 in s1))
          case NotInMultiSet() => Success(V.Bool(v0 !in s1))
          case _ => Failure(InvalidExpression(expr))
        }
      case _ => Failure(InvalidExpression(expr))
  }

  function method InterpSequences(expr: Expr, op: BinaryOps.Sequences, v0: V.T, v1: V.T)
    : PureInterpResult<V.T>
  {
    match (v0, v1)
      case (Seq(s0), Seq(s1)) =>
        match op {
          case SeqEq() => Success(V.Bool(s0 == s1))
          case SeqNeq() => Success(V.Bool(s0 != s1))
          case Prefix() => Success(V.Bool(s0 <= s1))
          case ProperPrefix() => Success(V.Bool(s0 < s1))
          case Concat() => Success(V.Seq(s0 + s1))
          case InSeq() => Failure(InvalidExpression(expr))
          case NotInSeq() => Failure(InvalidExpression(expr))
        }
      case (_, Seq(s1)) =>
        match op {
          case InSeq() => Success(V.Bool(v0 in s1))
          case NotInSeq() => Success(V.Bool(v0 !in s1))
          case _ => Failure(InvalidExpression(expr))
        }
      case _ => Failure(InvalidExpression(expr))
  }

  function method InterpMaps(expr: Expr, op: BinaryOps.Maps, v0: V.T, v1: V.T)
    : PureInterpResult<V.T>
  {
    match (v0, v1)
      case (Map(m0), Map(m1)) =>
        match op {
          case MapEq() => Success(V.Bool(m0 == m1))
          case MapNeq() => Success(V.Bool(m0 != m1))
          case MapMerge() => Success(V.Map(m0 + m1))
          case MapSubtraction() => Failure(InvalidExpression(expr))
          case InMap() => Failure(InvalidExpression(expr))
          case NotInMap() => Failure(InvalidExpression(expr))
        }
      case (Map(m0), Set(s1)) =>
        match op {
          case MapSubtraction() => Success(V.Map(m0 - s1))
          case _ => Failure(InvalidExpression(expr))
        }
      case (_, Map(m1)) =>
        match op {
          case InMap() => Success(V.Bool(v0 in m1))
          case NotInMap() => Success(V.Bool(v0 !in m1))
          case _ => Failure(InvalidExpression(expr))
        }
      case _ => Failure(InvalidExpression(expr))
  }
}
