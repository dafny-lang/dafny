include "CompilerCommon.dfy"

module Interp {
  module Value {
    import Ty = DafnyCompilerCommon.AST.Type

    datatype T =
      | Bool(b: bool)
      | Char(c: char)
      | Int(i: int)
      | Real(r: real)
      | BigOrdinal(o: ORDINAL)
      | BitVector(value: int)
      | Map(m: map<T, T>)
      | Multiset(ms: multiset<T>)
      | Seq(sq: seq<T>)
      | Set(st: set<T>)
    {
      predicate HasType(ty: Ty.Type) {
        match (this, ty) // FIXME tests on other side
          case (Bool(b), Bool()) => true
          case (Char(c), Char()) => true
          case (Int(i), Int()) => true
          case (Real(r), Real()) => true
          case (BigOrdinal(o), BigOrdinal()) => true
          case (BitVector(value), BitVector(width)) =>
            0 <= value < Pow2(width)
          case (Map(m), Collection(true, Map(kT), eT)) =>
            forall x | x in m :: x.HasType(kT) && m[x].HasType(eT)
          case (Multiset(ms), Collection(true, Multiset, eT)) =>
            forall x | x in ms :: x.HasType(eT)
          case (Seq(sq), Collection(true, Seq, eT)) =>
            forall x | x in sq :: x.HasType(eT)
          case (Set(st), Collection(true, Set, eT)) =>
            forall x | x in st :: x.HasType(eT)
          case (_, _) => false
      }
    }

    function method Pow2(n: nat): nat

    datatype Value = Value(ty: Ty.Type, v: T) {
      predicate Wf() { v.HasType(ty) }
    }

    // FIXME how do we define the interpreter to support :| without committing to a single interpretation of :|?
  }

  import opened DafnyCompilerCommon.AST
  import opened DafnyCompilerCommon.Predicates
  type Expr = AST.Expr.Expr
  type Type = AST.Type.Type
  import V = Value
  // FIXME reduce indirection

  datatype Result =
    | OK(v: Value.Value)
    | TypeError(e: Expr, t: Type) // FIXME rule out type errors through Wf predicate


  predicate method Pure1(e: Expr) {
    match e {
      case Literal(lit) => true
      case Apply(aop, args: seq<Expr>) =>
        match aop {
          case UnaryOp(uop: UnaryOp.Op) => true
          case BinaryOp(bop: BinaryOp.Op) => true
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
    AST.Expr.WellFormed(e) &&
    var FALSE := false;
    match e {
      case Literal(lit) => true
      case Apply(aop, args: seq<Expr>) =>
        match aop {
          case UnaryOp(uop: UnaryOp.Op) => FALSE
          case BinaryOp(bop: BinaryOp.Op) => true
          case DataConstructor(name: Path, typeArgs: seq<Type.Type>) => FALSE
          case Builtin(Display(_)) => FALSE
          case Builtin(Print) => false
          case MethodCall(classType, receiver, typeArgs) => false
          case FunctionCall() => FALSE
        }
      case Block(stmts: seq<Expr>) => false
      case If(cond: Expr, thn: Expr, els: Expr) => FALSE
      case Unsupported(_) => false
    }
  }

  predicate method SupportsInterp(e: Expr) {
    Predicates.Deep.All_Expr(e, SupportsInterp1)
  }

  function method InterpLiteral(a: AST.Expr.Literal) : V.T {
    match a
      case LitBool(b: bool) => V.Bool(b)
      case LitInt(i: int) => V.Int(i)
      case LitReal(r: real) => V.Real(r)
      case LitChar(c: string) => assume c != []; V.Char(c[0]) // FIXME
      case LitString(s: string, verbatim: bool) =>
        V.Seq(seq(|s|, i requires 0 <= i < |s| => V.Char(s[i])))
  }

  type Ctx = map<string, V.Value>

  function method InterpExpr(e: AST.Expr.Expr, ctx: Ctx := map[]) : (Ctx, V.T)
    requires SupportsInterp(e)
  {
    match e {
      case Literal(lit) => (ctx, InterpLiteral(lit))
      case Apply(aop, args: seq<Expr>) =>
        match aop {
          case UnaryOp(uop: UnaryOp.Op) => (ctx, V.Int(0))
          case BinaryOp(bop: BinaryOp.Op) => (ctx, V.Int(0))
        }
      case If(_, _, _) => assert false; (ctx, V.Int(0))
    }
  }
}
