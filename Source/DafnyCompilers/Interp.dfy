include "CompilerCommon.dfy"
include "Library.dfy"
include "Values.dfy"

module Interp {
  import Lib.Math
  import Lib.Debug
  import Lib.Seq

  import V = Values
  import DafnyCompilerCommon.AST.Types
  import DafnyCompilerCommon.AST.Exprs

  import opened Lib.Datatypes
  import opened DafnyCompilerCommon.Predicates

  // FIXME move
  predicate method Pure1(e: Exprs.T) {
    match e {
      case Var(_) => true
      case Literal(lit) => true
      case Abs(vars, body) => true
      case Apply(Lazy(op), args) =>
        true
      case Apply(Eager(op), args) =>
        match op {
          case UnaryOp(uop) => true
          case BinaryOp(bop) => true
          case TernaryOp(top) => true
          case Builtin(Display(_)) => true
          case Builtin(Print) => false
          case FunctionCall() => true
          case DataConstructor(name, typeArgs) => true
        }
      case Block(stmts) => true
      case If(cond, thn, els) => true
    }
  }

  predicate method Pure(e: Exprs.T) {
    Predicates.Deep.All_Expr(e, Pure1)
  }

  predicate method EagerOpSupportsInterp(op: Exprs.EagerOp) {
    match op {
      case UnaryOp(uop) => !uop.MemberSelect?
      case BinaryOp(bop) => !bop.BV? && !bop.Datatypes?
      case TernaryOp(top) => true
      case Builtin(Display(_)) => true
      case Builtin(Print()) => false
      case FunctionCall() => true
      case DataConstructor(name, typeArgs) => Debug.TODO(false)
    }
  }

  predicate method SupportsInterp1(e: Exprs.T) {
    AST.Exprs.WellFormed(e) &&
    match e {
      case Var(_) => true
      case Literal(lit) => true
      case Abs(vars, body) => true
      case Apply(Lazy(op), args) => true
      case Apply(Eager(op), args) => EagerOpSupportsInterp(op)
      case Block(stmts) => Debug.TODO(false)
      case If(cond, thn, els) => true
    }
  }

  // TODO: I'm not sure it was worth making this opaque.
  predicate method {:opaque} SupportsInterp(e: Exprs.T) {
    Predicates.Deep.All_Expr(e, SupportsInterp1)
  }

  lemma SupportsInterp_Pure(e: Exprs.T)
    requires SupportsInterp1(e)
    ensures Pure1(e)
  {}

  // TODO: rewrite as a shallow predicate applied through ``v.All``?
  predicate method WellFormedEqValue(v: V.T)
  // This predicate gives the constrainst we need to be able to *define* our equivalence relation
  // over values and actually *use* this relation to prove equivalence properties between expressions.
  //
  // The difficult point is linked to closures: when we apply transformations to the code, we often
  // apply them in a deep manner to the expressions (i.e., to all the subexpressions of an expression).
  // The problem is that it can have an effect on the closure values generated through the execution
  // by modifying their bodies, leading to discrepancies in the execution of the code (imagine the case
  // where we use closures as keys inside of maps).
  // The good news is that when those cases happen, we actually try to use an equality over values
  // which don't have a decidable equality: we solve the problem by forcing some subvalues to have
  // a decidable equality.
  {
    match v {
      case Bool(b) => true
      case Char(c) => true
      case Int(i) => true
      case Real(r) => true
      case BigOrdinal(o) => true
      case BitVector(width, val) =>
        0 <= val < Math.IntPow(2, width)
      case Map(m) =>
        && (forall x | x in m :: HasEqValue(x))
        && (forall x | x in m :: WellFormedEqValue(x) && WellFormedEqValue(m[x]))
      case Multiset(ms) =>
        && HasEqValue(v)
        && (forall x | x in ms :: WellFormedEqValue(x))
      case Seq(sq) =>
        && (forall x | x in sq :: WellFormedEqValue(x))
      case Set(st) =>
        && HasEqValue(v)
        && (forall x | x in st :: WellFormedEqValue(x))
      case Closure(ctx, vars, body) =>
        // TODO: is that enough?
        && (forall x | x in ctx.Values :: WellFormedEqValue(x))
    }
  }

  // TODO: rename to ValueHasEq
  predicate method HasEqValue(v: V.T)
  // Return true if the value supports a decidale equality.
  //
  // Note that this is a bit subtle for collections: any empty collection supports a decidable
  // equality, but non-empty collections support a decidable equality only if their elements
  // support one.
  {
    match v {
      case Bool(b) => true
      case Char(c) => true
      case Int(i) => true
      case Real(r) => true
      case BigOrdinal(o) => true
      case BitVector(width, val) => true
      case Map(m) =>
        forall x | x in m :: HasEqValue(x) && HasEqValue(m[x])
      case Multiset(ms) =>
        forall x | x in ms :: HasEqValue(x)
      case Seq(sq) =>
        forall x | x in sq :: HasEqValue(x)
      case Set(st) =>
        forall x | x in st :: HasEqValue(x)
      case Closure(ctx, vars, body) => false
    }
  }

  predicate method WellFormedValue1(v: V.T)
  // The *shallow* well-formedness predicate for values manipulated by the interpreter.
  {
    && v.Closure? ==> SupportsInterp(v.body)
    && v.WellFormed1()
  }

  predicate method WellFormedValue(v: V.T) {
    // Rk.: ``Value.All`` goes inside the closure contexts
    && v.All(WellFormedValue1)
    && WellFormedEqValue(v)
  }

  predicate method WellFormedContext(ctx: V.Context) {
    forall v' | v' in ctx.Values :: WellFormedValue(v')
  }

  type Type = Types.T
  type Context = c: V.Context | WellFormedContext(c)
  type Value = v: V.T | WellFormedValue(v) witness V.Bool(false)
  type Expr = e: Exprs.T | SupportsInterp(e) witness (reveal SupportsInterp(); Exprs.Literal(Exprs.LitInt(0)))

  // The type of well-formed values with a decidable equality
  type EqWV = v: V.T | WellFormedValue(v) && HasEqValue(v) witness V.Bool(false)

  // We need a value type height to prove that some functions terminate.
  function {:axiom} ValueTypeHeight(v: Value): nat

  // Axiom: the children of a collection have a smaller type than the collection's type
  lemma {:axiom} ValueTypeHeight_Children_Lem(v: Value)
    requires v.Map? || v.Multiset? || v.Seq? || v.Set?
    ensures forall x | x in v.Children() :: ValueTypeHeight(x) < ValueTypeHeight(v)
    // Special case for the keys of a map
    ensures v.Map? ==> (forall x | x in v.m :: ValueTypeHeight(x) < ValueTypeHeight(v))

  predicate InterpResultPred<A(0)>(p: (A,State) -> bool, r: InterpResult<A>) {
    match r {
      case Success(Return(x, ctx)) => p(x, ctx)
      case Failure(_) => true
    }
  }

  predicate PureInterpResultPred<A(0)>(p: A -> bool, r: PureInterpResult<A>) {
    match r {
      case Success(x) => p(x)
      case Failure(_) => true
    }
  }

  datatype State =
    State(locals: Context := map[])
  {
    static const Empty := State(map[]) // BUG(https://github.com/dafny-lang/dafny/issues/2120)
  }

  datatype Environment =
    Environment(fuel: nat, globals: Context := map[])

  datatype InterpReturn<+A> =
    | Return(ret: A, ctx: State)

  // FIXME many "Invalid" below should really be type errors

  datatype InterpError =
    | OutOfFuel(fn: Value)
    | TypeError(e: Expr, value: Value, expected: Type) // TODO rule out type errors through Wf predicate?
    | Invalid(e: Expr) // TODO rule out in Wf predicate?
    | OutOfIntBounds(x: int, low: Option<int>, high: Option<int>)
    | OutOfSeqBounds(collection: Value, idx: Value)
    | UnboundVariable(v: string)
    | SignatureMismatch(vars: seq<string>, argvs: seq<Value>)
    | DivisionByZero
  {
    function method ToString() : string {
      match this // TODO include values in messages
        case OutOfFuel(fn) => "Too many function evaluations"
        case TypeError(e, value, expected) => "Type mismatch"
        case Invalid(e) => "Invalid expression"
        case OutOfIntBounds(x, low, high) => "Out-of-bounds value"
        case OutOfSeqBounds(v, i) => "Out-of-bounds index"
        case UnboundVariable(v) => "Unbound variable '" + v + "'"
        case SignatureMismatch(vars, argvs) => "Wrong number of arguments in function call"
        case DivisionByZero() => "Division by zero"
    }
  }

  type InterpResult<+A> =
    Result<InterpReturn<A>, InterpError>

  type PureInterpResult<+A> =
    Result<A, InterpError>

  function method LiftPureResult<A>(ctx: State, r: PureInterpResult<A>)
    : InterpResult<A>
  {
    var v :- r;
    Success(Return(v, ctx))
  }

  function method InterpExpr(e: Expr, env: Environment, ctx: State := State.Empty)
    : (r: InterpResult<Value>)
    requires SupportsInterp(e)
    decreases env.fuel, e, 1
  {
    reveal SupportsInterp();
    Predicates.Deep.AllImpliesChildren(e, SupportsInterp1);
    match e {
      case Var(v) =>
        LiftPureResult(ctx, InterpVar(v, ctx, env))
      case Abs(vars, body) =>
        var cv: V.T := V.Closure(ctx.locals, vars, body);
        assert WellFormedValue(cv); // TODO: prove
        Success(Return(cv, ctx))
      case Literal(lit) =>
        Success(Return(InterpLiteral(lit), ctx))
      case Apply(Lazy(op), args: seq<Expr>) =>
        InterpLazy(e, env, ctx)
      case Apply(Eager(op), args: seq<Expr>) =>
        var Return(argvs, ctx) :- InterpExprs(args, env, ctx);
        LiftPureResult(ctx, match op {
            case UnaryOp(op: UnaryOp) =>
              InterpUnaryOp(e, op, argvs[0])
            case BinaryOp(bop: BinaryOp) =>
              assert !bop.BV? && !bop.Datatypes?;
              InterpBinaryOp(e, bop, argvs[0], argvs[1])
            case TernaryOp(top: TernaryOp) =>
              InterpTernaryOp(e, top, argvs[0], argvs[1], argvs[2])
            case Builtin(Display(ty)) =>
              InterpDisplay(e, ty.kind, argvs)
            case FunctionCall() =>
              InterpFunctionCall(e, env, argvs[0], argvs[1..])
          })
      case If(cond, thn, els) =>
        var Return(condv, ctx) :- InterpExprWithType(cond, Type.Bool, env, ctx);
        if condv.b then InterpExpr(thn, env, ctx) else InterpExpr(els, env, ctx)
    }
  }

  function method InterpVar(v: string, ctx: State, env: Environment)
    : PureInterpResult<Value>
  {
    match TryGetVariable(ctx.locals, v, UnboundVariable(v))
      case Success(val) => Success(val)
      case Failure(err) => TryGetVariable(env.globals, v, err)
  }

  function method {:opaque} TryGetVariable(ctx: Context, k: string, err: InterpError)
    : (r: PureInterpResult<Value>)
    ensures r.Success? ==> k in ctx && r.value == ctx[k]
    ensures r.Failure? ==> k !in ctx && r.error == err
  {
    TryGet(ctx, k, err)
  }

  function method {:opaque} TryGet<K, V>(m: map<K, V>, k: K, err: InterpError)
    : (r: PureInterpResult<V>)
    ensures r.Success? ==> k in m && r.value == m[k]
    ensures r.Failure? ==> k !in m && r.error == err
  {
    if k in m then Success(m[k]) else Failure(err)
  }

  function method TryGetPair<K, V>(m: map<K, V>, k: K, err: InterpError)
    : (r: PureInterpResult<(K, V)>)
    ensures r.Success? ==> k in m && r.value == (k, m[k])
    ensures r.Failure? ==> k !in m && r.error == err
  {
    if k in m then Success((k, m[k])) else Failure(err)
  }

  function method MapOfPairs<K, V>(pairs: seq<(K, V)>)
    : (m: map<K, V>)
    ensures forall k | k in m :: (k, m[k]) in pairs
  {
    if pairs == [] then map[]
    else
      var lastidx := |pairs| - 1;
      MapOfPairs(pairs[..lastidx])[pairs[lastidx].0 := pairs[lastidx].1]
  }

  function method InterpExprWithType(e: Expr, ty: Type, env: Environment, ctx: State)
    : (r: InterpResult<Value>)
    requires SupportsInterp(e)
    decreases env.fuel, e, 2
    ensures r.Success? ==> r.value.ret.HasType(ty)
  {
    reveal SupportsInterp();
    var Return(val, ctx) :- InterpExpr(e, env, ctx);
    :- Need(val.HasType(ty), TypeError(e, val, ty));
    Success(Return(val, ctx))
  }

  function method NeedType(e: Expr, val: Value, ty: Type)
    : (r: Outcome<InterpError>)
    ensures r.Pass? ==> val.HasType(ty)
  {
    Need(val.HasType(ty), TypeError(e, val, ty))
  }

  function method NeedTypes(es: seq<Expr>, vs: seq<Value>, ty: Type)
    : (r: Outcome<InterpError>)
    requires |es| == |vs|
    decreases |es|
    // DISCUSS: Replacing this with <==> doesn't verify
    ensures r.Pass? ==> forall v | v in vs :: v.HasType(ty)
    ensures r.Pass? <== forall v | v in vs :: v.HasType(ty)
  {
    if es == [] then
      assert vs == []; Pass
    else
      // DISCUSS: No `:-` for outcomes?
      // DISCUSS: should match accept multiple discriminands? (with lazy evaluation?)
      match NeedType(es[0], vs[0], ty)
        case Pass =>
          assert vs[0].HasType(ty);
          match NeedTypes(es[1..], vs[1..], ty) { // TODO check that compiler does this efficiently
            case Pass => assert forall v | v in vs[1..] :: v.HasType(ty); Pass
            case fail => fail
          }
        case fail => fail
  }

  function method {:opaque} InterpExprs(es: seq<Expr>, env: Environment, ctx: State)
    : (r: InterpResult<seq<Value>>)
    requires forall e | e in es :: SupportsInterp(e)
    decreases env.fuel, es
    ensures r.Success? ==> |r.value.ret| == |es|
  { // TODO generalize into a FoldResult function
    reveal SupportsInterp();
    if es == [] then Success(Return([], ctx))
    else
      var Return(v, ctx) :- InterpExpr(es[0], env, ctx);
      var Return(vs, ctx) :- InterpExprs(es[1..], env, ctx);
      Success(Return([v] + vs, ctx))
  }

  function method {:opaque} InterpLiteral(a: AST.Exprs.Literal) : (v: Value)
    ensures HasEqValue(v)
  {
    match a
      case LitBool(b: bool) => V.Bool(b)
      case LitInt(i: int) => V.Int(i)
      case LitReal(r: real) => V.Real(r)
      case LitChar(c: char) => V.Char(c)
      case LitString(s: string, verbatim: bool) =>
        var chars := seq(|s|, i requires 0 <= i < |s| => V.Char(s[i]));
        assert forall c | c in chars :: WellFormedValue(c);
        assert forall c | c in chars :: HasEqValue(c);
        V.Seq(chars)
  }

  function method {:opaque} InterpLazy(e: Expr, env: Environment, ctx: State)
    : (r: InterpResult<Value>)
    requires e.Apply? && e.aop.Lazy? && SupportsInterp(e)
    decreases env.fuel, e, 0
  {
    reveal SupportsInterp();
    Predicates.Deep.AllImpliesChildren(e, SupportsInterp1);
    var op, e0, e1 := e.aop.lOp, e.args[0], e.args[1];
    var Return(v0, ctx0) :- InterpExprWithType(e0, Type.Bool, env, ctx);
    match (op, v0)
      case (And, Bool(false)) => Success(Return(V.Bool(false), ctx0))
      case (Or,  Bool(true))  => Success(Return(V.Bool(true), ctx0))
      case (Imp, Bool(false)) => Success(Return(V.Bool(true), ctx0))
      case (_,   Bool(b)) =>
        assert op in {Exprs.And, Exprs.Or, Exprs.Imp};
        InterpExprWithType(e1, Type.Bool, env, ctx0)
  }

  // Alternate implementation of ``InterpLazy``: less efficient but more closely
  // matching intuition.
  function method {:opaque} InterpLazy_Eagerly(e: Expr, env: Environment, ctx: State)
    : (r: InterpResult<Value>)
    requires e.Apply? && e.aop.Lazy? && SupportsInterp(e)
    decreases env.fuel, e, 0
  {
    reveal SupportsInterp();
    Predicates.Deep.AllImpliesChildren(e, SupportsInterp1);
    var op, e0, e1 := e.aop.lOp, e.args[0], e.args[1];
    var Return(v0, ctx0) :- InterpExprWithType(e0, Type.Bool, env, ctx);
    var Return(v1, ctx1) :- InterpExprWithType(e1, Type.Bool, env, ctx0);
    match (op, v0, v1)
      case (And, Bool(b0), Bool(b1)) =>
        Success(Return(V.Bool(b0 && b1), if b0 then ctx1 else ctx0))
      case (Or,  Bool(b0), Bool(b1)) =>
        Success(Return(V.Bool(b0 || b1), if b0 then ctx0 else ctx1))
      case (Imp, Bool(b0), Bool(b1)) =>
        Success(Return(V.Bool(b0 ==> b1), if b0 then ctx1 else ctx0))
  }

  lemma InterpLazy_Complete(e: Expr, env: Environment, ctx: State)
    requires e.Apply? && e.aop.Lazy? && SupportsInterp(e)
    requires InterpLazy(e, env, ctx).Failure?
    ensures InterpLazy_Eagerly(e, env, ctx) == InterpLazy(e, env, ctx)
  {
    reveal SupportsInterp();
    reveal InterpLazy();
    reveal InterpLazy_Eagerly();
  }

  lemma InterpLazy_Eagerly_Sound(e: Expr, env: Environment, ctx: State)
    requires e.Apply? && e.aop.Lazy? && SupportsInterp(e)
    requires InterpLazy_Eagerly(e, env, ctx).Success?
    ensures InterpLazy_Eagerly(e, env, ctx) == InterpLazy(e, env, ctx)
  {
    reveal SupportsInterp();
    reveal InterpLazy();
    reveal InterpLazy_Eagerly();
  }

  function method {:opaque} InterpUnaryOp(expr: Expr, op: AST.UnaryOp, v0: Value)
    : (r: PureInterpResult<Value>)
    requires !op.MemberSelect?
  {
    match op
      case BVNot => :- Need(v0.BitVector?, Invalid(expr));
        Success(V.BitVector(v0.width, Math.IntPow(2, v0.width) - 1 - v0.value))
      case BoolNot => :- Need(v0.Bool?, Invalid(expr));
        Success(V.Bool(!v0.b))
      case SeqLength => :- Need(v0.Seq?, Invalid(expr));
        Success(V.Int(|v0.sq|))
      case SetCard => :- Need(v0.Set?, Invalid(expr));
        Success(V.Int(|v0.st|))
      case MultisetCard => :- Need(v0.Multiset?, Invalid(expr));
        Success(V.Int(|v0.ms|))
      case MapCard => :- Need(v0.Map?, Invalid(expr));
        Success(V.Int(|v0.m|))
  }

  function method {:opaque} InterpBinaryOp(expr: Expr, bop: AST.BinaryOp, v0: Value, v1: Value)
    : (r: PureInterpResult<Value>)
    requires !bop.BV? && !bop.Datatypes?
  {
    match bop
      case Numeric(op) => InterpBinaryNumeric(expr, op, v0, v1)
      case Logical(op) => InterpBinaryLogical(expr, op, v0, v1)
      case Eq(op) => // FIXME which types is this Eq applicable to (vs. the type-specific ones?)
        :- Need(HasEqValue(v0), Invalid(expr));
        :- Need(HasEqValue(v1), Invalid(expr));
        match op {
          case EqCommon() => Success(V.Bool(v0 == v1))
          case NeqCommon() => Success(V.Bool(v0 != v1))
        }
      // case BV(op) =>
      case Char(op) => InterpBinaryChar(expr, op, v0, v1)
      case Sets(op) => InterpBinarySets(expr, op, v0, v1)
      case Multisets(op) => InterpBinaryMultisets(expr, op, v0, v1)
      case Sequences(op) => InterpBinarySequences(expr, op, v0, v1)
      case Maps(op) => InterpBinaryMaps(expr, op, v0, v1)
      // case Datatypes(op) =>
  }

  function method InterpBinaryNumeric(expr: Expr, op: Exprs.BinaryOps.Numeric, v0: Value, v1: Value)
    : (r: PureInterpResult<Value>)
  {
    match (v0, v1) {
      // Separate functions to more easily check exhaustiveness
      case (Int(x1), Int(x2)) => InterpBinaryInt(expr, op, x1, x2)
      case (Char(x1), Char(x2)) => InterpBinaryNumericChar(expr, op, x1, x2)
      case (Real(x1), Real(x2)) => InterpBinaryReal(expr, op, x1, x2)
      case _ => Failure(Invalid(expr)) // FIXME: Wf
    }
  }

  function method CheckDivisionByZero(b: bool) : Outcome<InterpError> {
    if b then Fail(DivisionByZero) else Pass
  }

  function method InterpBinaryInt(expr: Expr, bop: AST.BinaryOps.Numeric, x1: int, x2: int)
    : (r: PureInterpResult<Value>)
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

  function method NeedIntBounds(x: int, low: int, high: int) : PureInterpResult<int> {
    :- Need(low <= x < high, OutOfIntBounds(x, Some(low), Some(high)));
    Success(x)
  }

  function method InterpBinaryNumericChar(expr: Expr, bop: AST.BinaryOps.Numeric, x1: char, x2: char)
    : (r: PureInterpResult<Value>)
  {
    match bop { // FIXME: These first four cases are not used (see InterpBinaryChar instead)
      case Lt() => Success(V.Bool(x1 < x2))
      case Le() => Success(V.Bool(x1 <= x2))
      case Ge() => Success(V.Bool(x1 >= x2))
      case Gt() => Success(V.Bool(x1 > x2))
      case Add() => var x :- NeedIntBounds(x1 as int + x2 as int, 0, 256); Success(V.Char(x as char))
      case Sub() => var x :- NeedIntBounds(x1 as int - x2 as int, 0, 256); Success(V.Char(x as char))
      case Mul() => Failure(Invalid(expr))
      case Div() => Failure(Invalid(expr))
      case Mod() => Failure(Invalid(expr))
    }
  }

  function method InterpBinaryReal(expr: Expr, bop: AST.BinaryOps.Numeric, x1: real, x2: real)
    : (r: PureInterpResult<Value>)
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
      case Mod() => Failure(Invalid(expr))
    }
  }

  function method InterpBinaryLogical(expr: Expr, op: Exprs.BinaryOps.Logical, v0: Value, v1: Value)
    : (r: PureInterpResult<Value>)
  {
    :- Need(v0.Bool? && v1.Bool?, Invalid(expr));
    match op
      case Iff() =>
        Success(V.Bool(v0.b <==> v1.b))
  }

  function method InterpBinaryChar(expr: Expr, op: AST.BinaryOps.Char, v0: Value, v1: Value)
    : (r: PureInterpResult<Value>)
  { // FIXME eliminate distinction between GtChar and GT?
    :- Need(v0.Char? && v1.Char?, Invalid(expr));
    match op
      case LtChar() =>
        Success(V.Bool(v0.c < v1.c))
      case LeChar() =>
        Success(V.Bool(v0.c <= v1.c))
      case GeChar() =>
        Success(V.Bool(v0.c >= v1.c))
      case GtChar() =>
        Success(V.Bool(v0.c > v1.c))
  }

  function method InterpBinarySets(expr: Expr, op: Exprs.BinaryOps.Sets, v0: Value, v1: Value)
    : (r: PureInterpResult<Value>)
  {
    // Rk.: we enforce through `WellFormedEqValue` that sets contain values with a decidable
    // equality.
    match op
      case SetEq() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st == v1.st))
      case SetNeq() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st != v1.st))
      case Subset() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st <= v1.st))
      case Superset() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st >= v1.st))
      case ProperSubset() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st < v1.st))
      case ProperSuperset() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st > v1.st))
      case Disjoint() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st !! v1.st))
      case Union() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Set(v0.st + v1.st))
      case Intersection() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Set(v0.st * v1.st))
      case SetDifference() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Set(v0.st - v1.st))
      case InSet() =>
        :- Need(HasEqValue(v0), Invalid(expr));
        :- Need(v1.Set?, Invalid(expr));
        Success(V.Bool(v0 in v1.st))
      case NotInSet() =>
        :- Need(HasEqValue(v0), Invalid(expr));
        :- Need(v1.Set?, Invalid(expr));
        Success(V.Bool(v0 !in v1.st))
  }

  function method InterpBinaryMultisets(expr: Expr, op: Exprs.BinaryOps.Multisets, v0: Value, v1: Value)
    : (r: PureInterpResult<Value>)
  {
    // Rk.: we enforce through `WellFormedEqValue` that multisets contain values with a decidable
    // equality.
    match op // DISCUSS
      case MultisetEq() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms == v1.ms))
      case MultisetNeq() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms != v1.ms))
      case MultiSubset() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms <= v1.ms))
      case MultiSuperset() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms >= v1.ms))
      case ProperMultiSubset() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms < v1.ms))
      case ProperMultiSuperset() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms > v1.ms))
      case MultisetDisjoint() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms !! v1.ms))
      case MultisetUnion() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Multiset(v0.ms + v1.ms))
      case MultisetIntersection() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Multiset(v0.ms * v1.ms))
      case MultisetDifference() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Multiset(v0.ms - v1.ms))
      case InMultiset() =>
        :- Need(HasEqValue(v0), Invalid(expr));
        :- Need(v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0 in v1.ms))
      case NotInMultiset() =>
        :- Need(HasEqValue(v0), Invalid(expr));
        :- Need(v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0 !in v1.ms))
      case MultisetSelect() =>
        :- Need(HasEqValue(v1), Invalid(expr));
        :- Need(v0.Multiset?, Invalid(expr));
        Success(V.Int(v0.ms[v1]))
  }

  function method InterpBinarySequences(expr: Expr, op: Exprs.BinaryOps.Sequences, v0: Value, v1: Value)
    : (r: PureInterpResult<Value>)
  {
    // Rk.: sequences don't necessarily contain values with decidable equality, we
    // thus dynamically check that we have what we need depending on the operation
    // we want to perform.
    // TODO: the dynamic checks for decidable equality may make the interpreter quite
    // slow. We might want to deduce this from a type check instead.
    match op
      case SeqEq() =>
        :- Need(v0.Seq? && v1.Seq?, Invalid(expr));
        :- Need(HasEqValue(v0), Invalid(expr)); // We need decidable equality
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        Success(V.Bool(v0.sq == v1.sq))
      case SeqNeq() =>
        :- Need(v0.Seq? && v1.Seq?, Invalid(expr));
        :- Need(HasEqValue(v0), Invalid(expr)); // We need decidable equality
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        Success(V.Bool(v0.sq != v1.sq))
      case Prefix() =>
        :- Need(v0.Seq? && v1.Seq?, Invalid(expr));
        :- Need(HasEqValue(v0), Invalid(expr)); // We need decidable equality
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        Success(V.Bool(v0.sq <= v1.sq))
      case ProperPrefix() =>
        :- Need(v0.Seq? && v1.Seq?, Invalid(expr));
        :- Need(HasEqValue(v0), Invalid(expr)); // We need decidable equality
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        Success(V.Bool(v0.sq < v1.sq))
      case Concat() => :- Need(v0.Seq? && v1.Seq?, Invalid(expr));
        Success(V.Seq(v0.sq + v1.sq))
      case InSeq() =>
        :- Need(v1.Seq?, Invalid(expr));
        :- Need(HasEqValue(v0), Invalid(expr)); // We need decidable equality
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        Success(V.Bool(v0 in v1.sq))
      case NotInSeq() =>
        :- Need(v1.Seq?, Invalid(expr));
        :- Need(HasEqValue(v0), Invalid(expr)); // We need decidable equality
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        Success(V.Bool(v0 !in v1.sq))
      case SeqDrop() =>
        :- NeedValidEndpoint(expr, v0, v1);
        Success(V.Seq(v0.sq[v1.i..]))
      case SeqTake() =>
        :- NeedValidEndpoint(expr, v0, v1);
        Success(V.Seq(v0.sq[..v1.i]))
      case SeqSelect() =>
        :- NeedValidIndex(expr, v0, v1);
        Success(v0.sq[v1.i])
  }

  function method InterpBinaryMaps(expr: Expr, op: Exprs.BinaryOps.Maps, v0: Value, v1: Value)
    : (r: PureInterpResult<Value>)
  {
    // Rk.: values in maps don't necessarily have a decidable equality. We thus perform
    // dynamic checks when we need one and fail if it is not the case.
    match op
      case MapEq() =>
        :- Need(v0.Map? && v1.Map?, Invalid(expr));
        :- Need(HasEqValue(v0), Invalid(expr)); // We need decidable equality
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        Success(V.Bool(v0.m == v1.m))
      case MapNeq() =>
        :- Need(v0.Map? && v1.Map?, Invalid(expr));
        :- Need(HasEqValue(v0), Invalid(expr)); // We need decidable equality
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        Success(V.Bool(v0.m != v1.m))
      case MapMerge() =>
        :- Need(v0.Map? && v1.Map?, Invalid(expr));
        Success(V.Map(v0.m + v1.m))
      case MapSubtraction() =>
        :- Need(v0.Map? && v1.Set?, Invalid(expr));
        Success(V.Map(v0.m - v1.st))
      case InMap() =>
        :- Need(v1.Map?, Invalid(expr));
        :- Need(HasEqValue(v0), Invalid(expr)); // We need decidable equality
        Success(V.Bool(v0 in v1.m))
      case NotInMap() =>
        :- Need(v1.Map?, Invalid(expr));
        :- Need(HasEqValue(v0), Invalid(expr)); // We need decidable equality
        Success(V.Bool(v0 !in v1.m))
      case MapSelect() =>
        :- Need(v0.Map?, Invalid(expr));
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        :- Need(v1 in v0.m, Invalid(expr));
        Success(v0.m[v1])
  }

  function method {:opaque} InterpTernaryOp(expr: Expr, top: AST.TernaryOp, v0: Value, v1: Value, v2: Value)
    : (r: PureInterpResult<Value>)
  {
    match top
      case Sequences(op) =>
        InterpTernarySequences(expr, op, v0, v1, v2)
      case Multisets(op) =>
        InterpTernaryMultisets(expr, op, v0, v1, v2)
      case Maps(op) =>
        InterpTernaryMaps(expr, op, v0, v1, v2)
  }

  function method NeedValidIndex(expr: Expr, vs: Value, vidx: Value)
    : Outcome<InterpError>
  { // FIXME no monadic operator for combining outcomes?
    match Need(vidx.Int? && vs.Seq?, Invalid(expr))
      case Pass() => Need(0 <= vidx.i < |vs.sq|, OutOfSeqBounds(vs, vidx))
      case fail => fail
  }

  function method NeedValidEndpoint(expr: Expr, vs: Value, vidx: Value)
    : Outcome<InterpError>
  {
    match Need(vidx.Int? && vs.Seq?, Invalid(expr))
      case Pass() => Need(0 <= vidx.i <= |vs.sq|, OutOfSeqBounds(vs, vidx))
      case fail => fail
  }

  function method InterpTernarySequences(expr: Expr, op: AST.TernaryOps.Sequences, v0: Value, v1: Value, v2: Value)
    : (r: PureInterpResult<Value>)
  {
    match op
      case SeqUpdate() =>
        :- NeedValidIndex(expr, v0, v1);
        Success(V.Seq(v0.sq[v1.i := v2]))
      case SeqSubseq() =>
        :- NeedValidEndpoint(expr, v0, v2);
        :- Need(v1.Int?, Invalid(expr));
        :- Need(0 <= v1.i <= v2.i, OutOfIntBounds(v1.i, Some(0), Some(v2.i)));
        Success(V.Seq(v0.sq[v1.i..v2.i]))
  }

  function method InterpTernaryMultisets(expr: Expr, op: AST.TernaryOps.Multisets, v0: Value, v1: Value, v2: Value)
    : (r: PureInterpResult<Value>)
  {
    match op
      case MultisetUpdate() =>
        :- Need(v0.Multiset?, Invalid(expr));
        :- Need(v2.Int? && v2.i >= 0, Invalid(expr));
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        Success(V.Multiset(v0.ms[v1 := v2.i]))
  }

  function method InterpTernaryMaps(expr: Expr, op: AST.TernaryOps.Maps, v0: Value, v1: Value, v2: Value)
    : (r: PureInterpResult<Value>)
  {
    match op
      case MapUpdate() =>
        :- Need(v0.Map?, Invalid(expr));
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        Success(V.Map(v0.m[v1 := v2]))
  }

  function method {:opaque} InterpDisplay(e: Expr, kind: Types.CollectionKind, argvs: seq<Value>)
    : (r: PureInterpResult<Value>)
  {
    match kind
      case Map(_) =>
        var m :- InterpMapDisplay(e, argvs);
        Success(V.Map(m))
      case Multiset() =>
        :- Need(forall i | 0 <= i < |argvs| :: HasEqValue(argvs[i]), Invalid(e)); // The elements must have a decidable equality
        var v := V.Multiset(multiset(argvs));
        assert WellFormedEqValue(v); // Doesn't work without this assert
        Success(v)
      case Seq() =>
        Success(V.Seq(argvs))
      case Set() =>
        :- Need(forall x | x in argvs :: HasEqValue(x), Invalid(e)); // The elements must have a decidable equality
        Success(V.Set(set s | s in argvs))
  }

  function method InterpMapDisplay(e: Expr, argvs: seq<Value>)
    : PureInterpResult<map<EqWV, Value>>
  {
    var pairs :- Seq.MapResult(argvs, argv => PairOfMapDisplaySeq(e, argv));
    Success(MapOfPairs(pairs))
  }

  function method PairOfMapDisplaySeq(e: Expr, argv: Value)
    : PureInterpResult<(EqWV, Value)>
  {
    :- Need(argv.Seq? && |argv.sq| == 2, Invalid(e));
    :- Need(HasEqValue(argv.sq[0]), Invalid(e));
    Success((argv.sq[0], argv.sq[1]))
  }

  function method {:opaque} BuildCallState(captured: Context, vars: seq<string>, vals: seq<Value>)
    : (ctx: State)
    requires |vars| == |vals|
  {
    State().(locals := captured + MapOfPairs(Seq.Zip(vars, vals)))
  }

  function method {:opaque} BuildCallState(base: Context, vars: seq<string>, vals: seq<Value>)
    : State
    requires |vars| == |vals|
  {
    State(locals := AugmentContext(base, vars, vals))
  }

  function method {:opaque} InterpFunctionCall(e: Expr, env: Environment, fn: Value, argvs: seq<Value>)
    : (r: PureInterpResult<Value>)
    decreases env.fuel, e, 0
  {
    :- Need(env.fuel > 0, OutOfFuel(fn));
    :- Need(fn.Closure?, Invalid(e));
    reveal SupportsInterp();
    Predicates.Deep.AllImpliesChildren(fn.body, SupportsInterp1);
    :- Need(|fn.vars| == |argvs|, SignatureMismatch(fn.vars, argvs));
    var ctx := BuildCallState(fn.ctx, fn.vars, argvs);
    var Return(val, ctx) :- InterpExpr(fn.body, env.(fuel := env.fuel - 1), ctx);
    Success(val)
  }
}
