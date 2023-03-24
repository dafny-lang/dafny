using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Numerics;
using System.Linq;
using System.Diagnostics;
using System.Security.AccessControl;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public abstract class Expression : TokenNode {
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(tok != null);
  }

  [System.Diagnostics.Contracts.Pure]
  public bool WasResolved() {
    return Type != null;
  }

  public Expression Resolved {
    get {
      Contract.Requires(WasResolved());  // should be called only on resolved expressions; this approximates that precondition
      Expression r = this;
      while (true) {
        Contract.Assert(r.WasResolved());  // this.WasResolved() implies anything it reaches is also resolved
        var rr = r as ConcreteSyntaxExpression;
        if (rr == null) {
          return r;
        }
        r = rr.ResolvedExpression;
        if (r == null) {
          // for a NegationExpression, we're willing to return its non-ResolveExpression form (since it is filled in
          // during a resolution phase after type checking and we may be called here during type checking)
          return rr is NegationExpression ? rr : null;
        }
      }
    }
  }

  public virtual IEnumerable<Expression> TerminalExpressions {
    get {
      yield return this;
    }
  }

  [FilledInDuringResolution] protected Type type;
  public Type Type {
    get {
      Contract.Ensures(type != null || Contract.Result<Type>() == null);  // useful in conjunction with postcondition of constructor
      return type == null ? null : type.Normalize();
    }
    set {
      Contract.Requires(!WasResolved());  // set it only once
      Contract.Requires(value != null);

      //modifies type;
      type = value.Normalize();
    }
  }
  /// <summary>
  /// This method can be used when .Type has been found to be erroneous and its current value
  /// would be unexpected by the rest of the resolver. This method then sets .Type to a neutral
  /// value.
  /// </summary>
  public void ResetTypeAssignment() {
    Contract.Requires(WasResolved());
    type = new InferredTypeProxy();
  }
#if TEST_TYPE_SYNONYM_TRANSPARENCY
    public void DebugTest_ChangeType(Type ty) {
      Contract.Requires(WasResolved());  // we're here to set it again
      Contract.Requires(ty != null);
      type = ty;
    }
#endif

  public Expression(IToken tok) {
    Contract.Requires(tok != null);
    Contract.Ensures(type == null);  // we would have liked to have written Type==null, but that's not admissible or provable

    this.tok = tok;
  }

  protected Expression(Cloner cloner, Expression original) {

    tok = cloner.Tok(original.tok);

    if (cloner.CloneResolvedFields && original.Type != null) {
      Type = original.Type;
    }
  }

  public override string ToString() {
    try {
      return Printer.ExprToString(DafnyOptions.DefaultImmutableOptions, this);
    } catch (Exception e) {
      return $"couldn't print expr because: {e.Message}";
    }
  }

  /// <summary>
  /// Returns the non-null subexpressions of the Expression.  To be called after the expression has been resolved; this
  /// means, for example, that any concrete syntax that resolves to some other expression will return the subexpressions
  /// of the resolved expression.
  /// </summary>
  public virtual IEnumerable<Expression> SubExpressions {
    get { yield break; }
  }

  /// <summary>
  /// Returns the list of types that appear in this expression proper (that is, not including types that
  /// may appear in subexpressions). Types occurring in substatements of the expression are not included.
  /// To be called after the expression has been resolved.
  /// </summary>
  public virtual IEnumerable<Type> ComponentTypes {
    get { yield break; }
  }

  public virtual bool IsImplicit {
    get { return false; }
  }

  public static IEnumerable<Expression> Conjuncts(Expression expr) {
    Contract.Requires(expr != null);
    Contract.Requires(expr.Type.IsBoolType);
    Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerable<Expression>>()));

    expr = StripParens(expr);
    if (expr is UnaryOpExpr unary && unary.Op == UnaryOpExpr.Opcode.Not) {
      foreach (Expression e in Disjuncts(unary.E)) {
        yield return Expression.CreateNot(e.tok, e);
      }
      yield break;

    } else if (expr is BinaryExpr bin) {
      if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.And) {
        foreach (Expression e in Conjuncts(bin.E0)) {
          yield return e;
        }
        foreach (Expression e in Conjuncts(bin.E1)) {
          yield return e;
        }
        yield break;
      }
    }

    yield return expr;
  }

  public static IEnumerable<Expression> Disjuncts(Expression expr) {
    Contract.Requires(expr != null);
    Contract.Requires(expr.Type.IsBoolType);
    Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerable<Expression>>()));

    expr = StripParens(expr);
    if (expr is UnaryOpExpr unary && unary.Op == UnaryOpExpr.Opcode.Not) {
      foreach (Expression e in Conjuncts(unary.E)) {
        yield return Expression.CreateNot(e.tok, e);
      }
      yield break;

    } else if (expr is BinaryExpr bin) {
      if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Or) {
        foreach (Expression e in Conjuncts(bin.E0)) {
          yield return e;
        }
        foreach (Expression e in Conjuncts(bin.E1)) {
          yield return e;
        }
        yield break;
      } else if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Imp) {
        foreach (Expression e in Conjuncts(bin.E0)) {
          yield return Expression.CreateNot(e.tok, e);
        }
        foreach (Expression e in Conjuncts(bin.E1)) {
          yield return e;
        }
        yield break;
      }
    }

    yield return expr;
  }

  /// <summary>
  /// Create a resolved expression of the form "e0 + e1"
  /// </summary>
  public static Expression CreateAdd(Expression e0, Expression e1) {
    Contract.Requires(e0 != null);
    Contract.Requires(e1 != null);
    Contract.Requires(
      (e0.Type.IsNumericBased(Type.NumericPersuasion.Int) && e1.Type.IsNumericBased(Type.NumericPersuasion.Int)) ||
      (e0.Type.IsNumericBased(Type.NumericPersuasion.Real) && e1.Type.IsNumericBased(Type.NumericPersuasion.Real)));
    Contract.Ensures(Contract.Result<Expression>() != null);
    var s = new BinaryExpr(e0.tok, BinaryExpr.Opcode.Add, e0, e1);
    s.ResolvedOp = BinaryExpr.ResolvedOpcode.Add;  // resolve here
    s.Type = e0.Type.NormalizeExpand();  // resolve here
    return s;
  }

  /// <summary>
  /// Create a resolved expression of the form "e0 * e1"
  /// </summary>
  public static Expression CreateMul(Expression e0, Expression e1) {
    Contract.Requires(e0 != null);
    Contract.Requires(e1 != null);
    Contract.Requires(
      (e0.Type.IsNumericBased(Type.NumericPersuasion.Int) && e1.Type.IsNumericBased(Type.NumericPersuasion.Int)) ||
      (e0.Type.IsNumericBased(Type.NumericPersuasion.Real) && e1.Type.IsNumericBased(Type.NumericPersuasion.Real)));
    Contract.Ensures(Contract.Result<Expression>() != null);
    var s = new BinaryExpr(e0.tok, BinaryExpr.Opcode.Mul, e0, e1);
    s.ResolvedOp = BinaryExpr.ResolvedOpcode.Mul;  // resolve here
    s.Type = e0.Type.NormalizeExpand();  // resolve here
    return s;
  }

  /// <summary>
  /// Create a resolved expression of the form "CVT(e0) - CVT(e1)", where "CVT" is either "int" (if
  /// e0.Type is an integer-based numeric type) or "real" (if e0.Type is a real-based numeric type).
  /// </summary>
  public static Expression CreateSubtract_TypeConvert(Expression e0, Expression e1) {
    Contract.Requires(e0 != null);
    Contract.Requires(e1 != null);
    Contract.Requires(
      (e0.Type.IsNumericBased(Type.NumericPersuasion.Int) && e1.Type.IsNumericBased(Type.NumericPersuasion.Int)) ||
      (e0.Type.IsNumericBased(Type.NumericPersuasion.Real) && e1.Type.IsNumericBased(Type.NumericPersuasion.Real)) ||
      (e0.Type.IsBitVectorType && e1.Type.IsBitVectorType) ||
      (e0.Type.IsCharType && e1.Type.IsCharType));
    Contract.Ensures(Contract.Result<Expression>() != null);

    Type toType;
    if (e0.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
      toType = Type.Int;
    } else if (e0.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
      toType = Type.Real;
    } else {
      Contract.Assert(e0.Type.IsBitVectorType || e0.Type.IsCharType);
      toType = Type.Int; // convert char and bitvectors to int
    }
    e0 = CastIfNeeded(e0, toType);
    e1 = CastIfNeeded(e1, toType);
    return CreateSubtract(e0, e1);
  }

  private static Expression CastIfNeeded(Expression expr, Type toType) {
    if (!expr.Type.Equals(toType)) {
      var cast = new ConversionExpr(expr.tok, expr, toType);
      cast.Type = toType;
      return cast;
    } else {
      return expr;
    }
  }

  /// <summary>
  /// Create a resolved expression of the form "e0 - e1"
  /// </summary>
  public static Expression CreateSubtract(Expression e0, Expression e1) {
    Contract.Requires(e0 != null);
    Contract.Requires(e0.Type != null);
    Contract.Requires(e1 != null);
    Contract.Requires(e1.Type != null);
    Contract.Requires(
      (e0.Type.IsNumericBased(Type.NumericPersuasion.Int) && e1.Type.IsNumericBased(Type.NumericPersuasion.Int)) ||
      (e0.Type.IsNumericBased(Type.NumericPersuasion.Real) && e1.Type.IsNumericBased(Type.NumericPersuasion.Real)) ||
      (e0.Type.IsBigOrdinalType && e1.Type.IsBigOrdinalType));
    Contract.Ensures(Contract.Result<Expression>() != null);
    var s = new BinaryExpr(e0.tok, BinaryExpr.Opcode.Sub, e0, e1);
    s.ResolvedOp = BinaryExpr.ResolvedOpcode.Sub;  // resolve here
    s.Type = e0.Type.NormalizeExpand();  // resolve here (and it's important to remove any constraints)
    return s;
  }

  /// <summary>
  /// Create a resolved expression of the form "e0 - e1".
  /// Optimization: If either "e0" or "e1" is the literal denoting the empty set, then just return "e0".
  /// </summary>
  public static Expression CreateSetDifference(Expression e0, Expression e1) {
    Contract.Requires(e0 != null);
    Contract.Requires(e0.Type != null);
    Contract.Requires(e1 != null);
    Contract.Requires(e1.Type != null);
    Contract.Requires(e0.Type.AsSetType != null && e1.Type.AsSetType != null);
    Contract.Ensures(Contract.Result<Expression>() != null);
    if (LiteralExpr.IsEmptySet(e0) || LiteralExpr.IsEmptySet(e1)) {
      return e0;
    }
    var s = new BinaryExpr(e0.tok, BinaryExpr.Opcode.Sub, e0, e1) {
      ResolvedOp = BinaryExpr.ResolvedOpcode.SetDifference,
      Type = e0.Type.NormalizeExpand() // important to remove any constraints
    };
    return s;
  }

  /// <summary>
  /// Create a resolved expression of the form "e0 - e1".
  /// Optimization: If either "e0" or "e1" is the literal denoting the empty multiset, then just return "e0".
  /// </summary>
  public static Expression CreateMultisetDifference(Expression e0, Expression e1) {
    Contract.Requires(e0 != null);
    Contract.Requires(e0.Type != null);
    Contract.Requires(e1 != null);
    Contract.Requires(e1.Type != null);
    Contract.Requires(e0.Type.AsMultiSetType != null && e1.Type.AsMultiSetType != null);
    Contract.Ensures(Contract.Result<Expression>() != null);
    if (LiteralExpr.IsEmptyMultiset(e0) || LiteralExpr.IsEmptyMultiset(e1)) {
      return e0;
    }
    var s = new BinaryExpr(e0.tok, BinaryExpr.Opcode.Sub, e0, e1) {
      ResolvedOp = BinaryExpr.ResolvedOpcode.MultiSetDifference,
      Type = e0.Type.NormalizeExpand() // important to remove any constraints
    };
    return s;
  }

  /// <summary>
  /// Create a resolved expression of the form "|e|"
  /// </summary>
  public static Expression CreateCardinality(Expression e, BuiltIns builtIns) {
    Contract.Requires(e != null);
    Contract.Requires(e.Type != null);
    Contract.Requires(e.Type.AsSetType != null || e.Type.AsMultiSetType != null || e.Type.AsSeqType != null);
    Contract.Ensures(Contract.Result<Expression>() != null);
    var s = new UnaryOpExpr(e.tok, UnaryOpExpr.Opcode.Cardinality, e) {
      Type = builtIns.Nat()
    };
    return s;
  }

  /// <summary>
  /// Create a resolved expression of the form "e + n"
  /// </summary>
  public static Expression CreateIncrement(Expression e, int n) {
    Contract.Requires(e != null);
    Contract.Requires(e.Type != null);
    Contract.Requires(e.Type.IsNumericBased(Type.NumericPersuasion.Int));
    Contract.Requires(0 <= n);
    Contract.Ensures(Contract.Result<Expression>() != null);
    if (n == 0) {
      return e;
    }
    var nn = CreateIntLiteral(e.tok, n);
    return CreateAdd(e, nn);
  }

  /// <summary>
  /// Create a resolved expression of the form "e - n"
  /// </summary>
  public static Expression CreateDecrement(Expression e, int n, Type ty = null) {
    Contract.Requires(e != null);
    Contract.Requires(e.Type.IsNumericBased(Type.NumericPersuasion.Int));
    Contract.Requires(0 <= n);
    Contract.Ensures(Contract.Result<Expression>() != null);
    if (n == 0) {
      return e;
    }
    var nn = CreateIntLiteral(e.tok, n, ty);
    return CreateSubtract(e, nn);
  }

  /// <summary>
  /// Create a resolved expression of the form "n"
  /// </summary>
  public static Expression CreateIntLiteral(IToken tok, int n, Type ty = null) {
    Contract.Requires(tok != null);
    Contract.Requires(n != int.MinValue);
    if (0 <= n) {
      var nn = new LiteralExpr(tok, n);
      nn.Type = ty ?? Type.Int;
      return nn;
    } else {
      return CreateDecrement(CreateIntLiteral(tok, 0, ty), -n, ty);
    }
  }

  /// <summary>
  /// Create a resolved expression of the form "x"
  /// </summary>
  public static Expression CreateRealLiteral(IToken tok, BaseTypes.BigDec x) {
    Contract.Requires(tok != null);
    var nn = new LiteralExpr(tok, x);
    nn.Type = Type.Real;
    return nn;
  }

  /// <summary>
  /// Create a resolved expression of the form "n", for either type "int" or type "ORDINAL".
  /// </summary>
  public static Expression CreateNatLiteral(IToken tok, int n, Type ty) {
    Contract.Requires(tok != null);
    Contract.Requires(0 <= n);
    Contract.Requires(ty.IsNumericBased(Type.NumericPersuasion.Int) || ty is BigOrdinalType);
    var nn = new LiteralExpr(tok, n);
    nn.Type = ty;
    return nn;
  }

  /// <summary>
  /// Create a resolved expression for a bool b
  /// </summary>
  public static LiteralExpr CreateBoolLiteral(IToken tok, bool b) {
    Contract.Requires(tok != null);
    var lit = new LiteralExpr(tok, b);
    lit.Type = Type.Bool;  // resolve here
    return lit;
  }

  /// <summary>
  /// Create a resolved expression for a string s
  /// </summary>
  public static LiteralExpr CreateStringLiteral(IToken tok, string s) {
    Contract.Requires(tok != null);
    Contract.Requires(s != null);
    var lit = new StringLiteralExpr(tok, s, true);
    lit.Type = new SeqType(new CharType());  // resolve here
    return lit;
  }

  /// <summary>
  /// Returns "expr", but with all outer layers of parentheses removed.
  /// This method can be called before resolution.
  /// </summary>
  public static Expression StripParens(Expression expr) {
    while (true) {
      var e = expr as ParensExpression;
      if (e == null) {
        return expr;
      }
      expr = e.E;
    }
  }

  /// <summary>
  /// Returns "expr", but with all outer layers of parentheses and casts removed.
  /// This method can be called before resolution.
  /// </summary>
  public static Expression StripParensAndCasts(Expression expr) {
    while (true) {
      if (expr is ParensExpression parens) {
        expr = parens.E;
      } else if (expr is ConversionExpr cast) {
        expr = cast.E;
      } else {
        return expr;
      }
    }
  }

  public static ThisExpr AsThis(Expression expr) {
    Contract.Requires(expr != null);
    return StripParens(expr) as ThisExpr;
  }

  /// <summary>
  /// If "expr" denotes a boolean literal "b", then return "true" and set "value" to "b".
  /// Otherwise, return "false" (and the value of "value" should not be used by the caller).
  /// This method can be called before resolution.
  /// </summary>
  public static bool IsBoolLiteral(Expression expr, out bool value) {
    Contract.Requires(expr != null);
    var e = StripParens(expr) as LiteralExpr;
    if (e != null && e.Value is bool) {
      value = (bool)e.Value;
      return true;
    } else {
      value = false;  // to please compiler
      return false;
    }
  }

  /// <summary>
  /// If "expr" denotes an integer literal "x", then return "true" and set "value" to "x".
  /// Otherwise, return "false" (and the value of "value" should not be used by the caller).
  /// This method can be called before resolution.
  /// </summary>
  public static bool IsIntLiteral(Expression expr, out BigInteger value) {
    Contract.Requires(expr != null);
    var e = StripParens(expr) as LiteralExpr;
    if (e != null && e.Value is int x) {
      value = new BigInteger(x);
      return true;
    } else if (e != null && e.Value is BigInteger xx) {
      value = xx;
      return true;
    } else {
      value = BigInteger.Zero; // to please compiler
      return false;
    }
  }

  /// <summary>
  /// Returns "true" if "expr" denotes the empty set (for "iset", "set", or "multiset").
  /// This method can be called before resolution.
  /// </summary>
  public static bool IsEmptySetOrMultiset(Expression expr) {
    Contract.Requires(expr != null);
    expr = StripParens(expr);
    return (expr is SetDisplayExpr && ((SetDisplayExpr)expr).Elements.Count == 0) ||
           (expr is MultiSetDisplayExpr && ((MultiSetDisplayExpr)expr).Elements.Count == 0);
  }

  /// <summary>
  /// Create a resolved ParensExpression around a given resolved expression "e".
  /// </summary>
  public static Expression CreateParensExpression(IToken tok, Expression e) {
    return new ParensExpression(tok, e) { Type = e.Type, ResolvedExpression = e };
  }

  public static Expression CreateNot(IToken tok, Expression e) {
    Contract.Requires(tok != null);
    Contract.Requires(e != null && e.Type != null && e.Type.IsBoolType);

    e = StripParens(e);
    if (e is UnaryOpExpr unary && unary.Op == UnaryOpExpr.Opcode.Not) {
      return unary.E;
    }

    if (e is BinaryExpr bin) {
      var negatedOp = BinaryExpr.ResolvedOpcode.Add; // let "Add" stand for "no negated operator"
      switch (bin.ResolvedOp) {
        case BinaryExpr.ResolvedOpcode.EqCommon:
          negatedOp = BinaryExpr.ResolvedOpcode.NeqCommon;
          break;
        case BinaryExpr.ResolvedOpcode.SetEq:
          negatedOp = BinaryExpr.ResolvedOpcode.SetNeq;
          break;
        case BinaryExpr.ResolvedOpcode.MultiSetEq:
          negatedOp = BinaryExpr.ResolvedOpcode.MultiSetNeq;
          break;
        case BinaryExpr.ResolvedOpcode.SeqEq:
          negatedOp = BinaryExpr.ResolvedOpcode.SeqNeq;
          break;
        case BinaryExpr.ResolvedOpcode.MapEq:
          negatedOp = BinaryExpr.ResolvedOpcode.MapNeq;
          break;
        case BinaryExpr.ResolvedOpcode.NeqCommon:
          negatedOp = BinaryExpr.ResolvedOpcode.EqCommon;
          break;
        case BinaryExpr.ResolvedOpcode.SetNeq:
          negatedOp = BinaryExpr.ResolvedOpcode.SetEq;
          break;
        case BinaryExpr.ResolvedOpcode.MultiSetNeq:
          negatedOp = BinaryExpr.ResolvedOpcode.MultiSetEq;
          break;
        case BinaryExpr.ResolvedOpcode.SeqNeq:
          negatedOp = BinaryExpr.ResolvedOpcode.SeqEq;
          break;
        case BinaryExpr.ResolvedOpcode.MapNeq:
          negatedOp = BinaryExpr.ResolvedOpcode.MapEq;
          break;
        default:
          break;
      }
      if (negatedOp != BinaryExpr.ResolvedOpcode.Add) {
        return new BinaryExpr(bin.tok, BinaryExpr.ResolvedOp2SyntacticOp(negatedOp), bin.E0, bin.E1) {
          ResolvedOp = negatedOp,
          Type = bin.Type
        };
      }
    }

    return new UnaryOpExpr(tok, UnaryOpExpr.Opcode.Not, e) {
      Type = Type.Bool
    };
  }

  /// <summary>
  /// Create a resolved expression of the form "e0 LESS e1"
  /// Works for integers, reals, bitvectors, chars, and ORDINALs.
  /// </summary>
  public static Expression CreateLess(Expression e0, Expression e1) {
    Contract.Requires(e0 != null && e0.Type != null);
    Contract.Requires(e1 != null && e1.Type != null);
    Contract.Requires(
      (e0.Type.IsNumericBased(Type.NumericPersuasion.Int) && e1.Type.IsNumericBased(Type.NumericPersuasion.Int)) ||
      (e0.Type.IsNumericBased(Type.NumericPersuasion.Real) && e1.Type.IsNumericBased(Type.NumericPersuasion.Real)) ||
      (e0.Type.IsBitVectorType && e1.Type.IsBitVectorType) ||
      (e0.Type.IsCharType && e1.Type.IsCharType) ||
      (e0.Type.IsBigOrdinalType && e1.Type.IsBigOrdinalType));
    Contract.Ensures(Contract.Result<Expression>() != null);
    return new BinaryExpr(e0.tok, BinaryExpr.Opcode.Lt, e0, e1) {
      ResolvedOp = e0.Type.IsCharType ? BinaryExpr.ResolvedOpcode.LtChar : BinaryExpr.ResolvedOpcode.Lt,
      Type = Type.Bool
    };
  }

  /// <summary>
  /// Create a resolved expression of the form "e0 ATMOST e1".
  /// Works for integers, reals, bitvectors, chars, and ORDINALs.
  /// </summary>
  public static Expression CreateAtMost(Expression e0, Expression e1) {
    Contract.Requires(e0 != null && e0.Type != null);
    Contract.Requires(e1 != null && e1.Type != null);
    Contract.Requires(
      (e0.Type.IsNumericBased(Type.NumericPersuasion.Int) && e1.Type.IsNumericBased(Type.NumericPersuasion.Int)) ||
      (e0.Type.IsNumericBased(Type.NumericPersuasion.Real) && e1.Type.IsNumericBased(Type.NumericPersuasion.Real)) ||
      (e0.Type.IsBitVectorType && e1.Type.IsBitVectorType) ||
      (e0.Type.IsCharType && e1.Type.IsCharType) ||
      (e0.Type.IsBigOrdinalType && e1.Type.IsBigOrdinalType));
    Contract.Ensures(Contract.Result<Expression>() != null);
    return new BinaryExpr(e0.tok, BinaryExpr.Opcode.Le, e0, e1) {
      ResolvedOp = e0.Type.IsCharType ? BinaryExpr.ResolvedOpcode.LeChar : BinaryExpr.ResolvedOpcode.Le,
      Type = Type.Bool
    };
  }

  public static Expression CreateEq(Expression e0, Expression e1, Type ty) {
    Contract.Requires(e0 != null);
    Contract.Requires(e1 != null);
    Contract.Requires(ty != null);
    var eq = new BinaryExpr(e0.tok, BinaryExpr.Opcode.Eq, e0, e1);
    if (ty is SetType) {
      eq.ResolvedOp = BinaryExpr.ResolvedOpcode.SetEq;
    } else if (ty is SeqType) {
      eq.ResolvedOp = BinaryExpr.ResolvedOpcode.SeqEq;
    } else if (ty is MultiSetType) {
      eq.ResolvedOp = BinaryExpr.ResolvedOpcode.MultiSetEq;
    } else if (ty is MapType) {
      eq.ResolvedOp = BinaryExpr.ResolvedOpcode.MapEq;
    } else {
      eq.ResolvedOp = BinaryExpr.ResolvedOpcode.EqCommon;
    }
    eq.type = Type.Bool;
    return eq;
  }

  /// <summary>
  /// Create a resolved expression of the form "e0 && e1"
  /// </summary>
  public static Expression CreateAnd(Expression a, Expression b, bool allowSimplification = true) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    Contract.Requires(a.Type.IsBoolType && b.Type.IsBoolType);
    Contract.Ensures(Contract.Result<Expression>() != null);
    if (allowSimplification && LiteralExpr.IsTrue(a)) {
      return b;
    } else if (allowSimplification && LiteralExpr.IsTrue(b)) {
      return a;
    } else {
      var and = new BinaryExpr(a.tok, BinaryExpr.Opcode.And, a, b);
      and.ResolvedOp = BinaryExpr.ResolvedOpcode.And;  // resolve here
      and.Type = Type.Bool;  // resolve here
      return and;
    }
  }

  /// <summary>
  /// Create a resolved expression of the form "e0 ==> e1"
  /// </summary>
  public static Expression CreateImplies(Expression a, Expression b, bool allowSimplification = true) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    Contract.Requires(a.Type.IsBoolType && b.Type.IsBoolType);
    Contract.Ensures(Contract.Result<Expression>() != null);
    if (allowSimplification && (LiteralExpr.IsTrue(a) || LiteralExpr.IsTrue(b))) {
      return b;
    } else {
      var imp = new BinaryExpr(a.tok, BinaryExpr.Opcode.Imp, a, b);
      imp.ResolvedOp = BinaryExpr.ResolvedOpcode.Imp;  // resolve here
      imp.Type = Type.Bool;  // resolve here
      return imp;
    }
  }

  /// <summary>
  /// Create a resolved expression of the form "e0 || e1"
  /// </summary>
  public static Expression CreateOr(Expression a, Expression b, bool allowSimplification = true) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    Contract.Requires(a.Type.IsBoolType && b.Type.IsBoolType);
    Contract.Ensures(Contract.Result<Expression>() != null);
    if (allowSimplification && LiteralExpr.IsTrue(a)) {
      return a;
    } else if (allowSimplification && LiteralExpr.IsTrue(b)) {
      return b;
    } else {
      var or = new BinaryExpr(a.tok, BinaryExpr.Opcode.Or, a, b);
      or.ResolvedOp = BinaryExpr.ResolvedOpcode.Or;  // resolve here
      or.Type = Type.Bool;  // resolve here
      return or;
    }
  }

  /// <summary>
  /// Create a resolved expression of the form "if test then e0 else e1"
  /// </summary>
  public static Expression CreateITE(Expression test, Expression e0, Expression e1) {
    Contract.Requires(test != null);
    Contract.Requires(e0 != null);
    Contract.Requires(e1 != null);
    Contract.Requires(test.Type.IsBoolType && e0.Type.Equals(e1.Type));
    Contract.Ensures(Contract.Result<Expression>() != null);
    var ite = new ITEExpr(test.tok, false, test, e0, e1);
    ite.Type = e0.type;  // resolve here
    return ite;
  }

  /// <summary>
  /// Create a resolved case expression for a match expression
  /// </summary>
  public static MatchCaseExpr CreateMatchCase(MatchCaseExpr old_case, Expression new_body) {
    Contract.Requires(old_case != null);
    Contract.Requires(new_body != null);
    Contract.Ensures(Contract.Result<MatchCaseExpr>() != null);

    var cloner = new Cloner(true);
    var newVars = old_case.Arguments.ConvertAll(bv => cloner.CloneBoundVar(bv, false));
    new_body = VarSubstituter(old_case.Arguments.ConvertAll<NonglobalVariable>(x => (NonglobalVariable)x), newVars, new_body);

    var new_case = new MatchCaseExpr(old_case.tok, old_case.Ctor, old_case.FromBoundVar, newVars, new_body, old_case.Attributes);

    new_case.Ctor = old_case.Ctor; // resolve here
    return new_case;
  }

  /// <summary>
  /// Create a match expression with a resolved type
  /// </summary>
  public static Expression CreateMatch(IToken tok, Expression src, List<MatchCaseExpr> cases, Type type) {
    MatchExpr e = new MatchExpr(tok, src, cases, false);
    e.Type = type;  // resolve here

    return e;
  }

  /// <summary>
  /// Create a let expression with a resolved type and fresh variables
  /// </summary>
  public static Expression CreateLet(IToken tok, List<CasePattern<BoundVar>> LHSs, List<Expression> RHSs, Expression body, bool exact) {
    Contract.Requires(tok != null);
    Contract.Requires(LHSs != null && RHSs != null);
    Contract.Requires(LHSs.Count == RHSs.Count);
    Contract.Requires(body != null);

    var cloner = new Cloner(true);
    var newLHSs = LHSs.ConvertAll(cloner.CloneCasePattern);

    var oldVars = new List<BoundVar>();
    LHSs.Iter(p => oldVars.AddRange(p.Vars));
    var newVars = new List<BoundVar>();
    newLHSs.Iter(p => newVars.AddRange(p.Vars));
    body = VarSubstituter(oldVars.ConvertAll<NonglobalVariable>(x => (NonglobalVariable)x), newVars, body);

    var let = new LetExpr(tok, newLHSs, RHSs, body, exact);
    let.Type = body.Type;  // resolve here
    return let;
  }

  /// <summary>
  /// Create a quantifier expression with a resolved type and fresh variables
  /// Optionally replace the old body with the supplied argument
  /// </summary>
  public static Expression CreateQuantifier(QuantifierExpr expr, bool forall, Expression body = null) {
    Contract.Requires(expr != null);

    var cloner = new Cloner(true);
    var newVars = expr.BoundVars.ConvertAll(bv => cloner.CloneBoundVar(bv, false));

    if (body == null) {
      body = expr.Term;
    }

    body = VarSubstituter(expr.BoundVars.ConvertAll<NonglobalVariable>(x => (NonglobalVariable)x), newVars, body);

    QuantifierExpr q;
    if (forall) {
      q = new ForallExpr(expr.tok, expr.RangeToken, newVars, expr.Range, body, expr.Attributes);
    } else {
      q = new ExistsExpr(expr.tok, expr.RangeToken, newVars, expr.Range, body, expr.Attributes);
    }
    q.Type = Type.Bool;

    return q;
  }

  /// <summary>
  /// Create a resolved IdentifierExpr (whose token is that of the variable)
  /// </summary>
  public static Expression CreateIdentExpr(IVariable v) {
    Contract.Requires(v != null);
    var e = new IdentifierExpr(v.Tok, v.Name);
    e.Var = v;  // resolve here
    e.type = v.Type;  // resolve here
    return e;
  }

  public static Expression VarSubstituter(List<NonglobalVariable> oldVars, List<BoundVar> newVars, Expression e, Dictionary<TypeParameter, Type> typeMap = null) {
    Contract.Requires(oldVars != null && newVars != null);
    Contract.Requires(oldVars.Count == newVars.Count);

    Dictionary<IVariable, Expression/*!*/> substMap = new Dictionary<IVariable, Expression>();
    if (typeMap == null) {
      typeMap = new Dictionary<TypeParameter, Type>();
    }

    for (int i = 0; i < oldVars.Count; i++) {
      var id = new IdentifierExpr(newVars[i].tok, newVars[i].Name);
      id.Var = newVars[i];    // Resolve here manually
      id.Type = newVars[i].Type;  // Resolve here manually
      substMap.Add(oldVars[i], id);
    }

    Substituter sub = new Substituter(null, substMap, typeMap);
    return sub.Substitute(e);
  }

  /// <summary>
  /// Returns the string literal underlying an actual string literal (not as a sequence display of characters)
  /// </summary>
  /// <returns></returns>
  public string AsStringLiteral() {
    var le = this as StringLiteralExpr;
    return le == null ? null : le.Value as string;
  }

  public override IEnumerable<Node> Children => SubExpressions;
  public override IEnumerable<Node> PreResolveChildren => Children;
}

public class LiteralExpr : Expression {
  /// <summary>
  /// One of the following:
  ///   * 'null' for the 'null' literal (a special case of which is the subclass StaticReceiverExpr)
  ///   * a bool for a bool literal
  ///   * a BigInteger for int literal
  ///   * a BaseTypes.BigDec for a (rational) real literal
  ///   * a string for a char literal
  ///     This case always uses the subclass CharLiteralExpr.
  ///     Note, a string is stored to keep any escape sequence, since this simplifies printing of the character
  ///     literal, both when pretty printed as a Dafny expression and when being compiled into C# code.  The
  ///     parser checks the validity of any escape sequence and the verifier deals with turning such into a
  ///     single character value.
  ///   * a string for a string literal
  ///     This case always uses the subclass StringLiteralExpr.
  ///     Note, the string is stored with all escapes as characters.  For example, the input string "hello\n" is
  ///     stored in a LiteralExpr has being 7 characters long, whereas the Dafny (and C#) length of this string is 6.
  ///     This simplifies printing of the string, both when pretty printed as a Dafny expression and when being
  ///     compiled into C# code.  The parser checks the validity of the escape sequences and the verifier deals
  ///     with turning them into single characters.
  /// </summary>
  public readonly object Value;

  [System.Diagnostics.Contracts.Pure]
  public static bool IsTrue(Expression e) {
    Contract.Requires(e != null);
    return Expression.IsBoolLiteral(e, out var value) && value;
  }

  public static bool IsEmptySet(Expression e) {
    Contract.Requires(e != null);
    return StripParens(e) is SetDisplayExpr display && display.Elements.Count == 0;
  }

  public static bool IsEmptyMultiset(Expression e) {
    Contract.Requires(e != null);
    return StripParens(e) is MultiSetDisplayExpr display && display.Elements.Count == 0;
  }

  public static bool IsEmptySequence(Expression e) {
    Contract.Requires(e != null);
    return StripParens(e) is SeqDisplayExpr display && display.Elements.Count == 0;
  }

  public LiteralExpr(IToken tok)
    : base(tok) {  // represents the Dafny literal "null"
    Contract.Requires(tok != null);
    this.Value = null;
  }

  public LiteralExpr(IToken tok, BigInteger n)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(0 <= n.Sign);
    this.Value = n;
  }

  public LiteralExpr(IToken tok, BaseTypes.BigDec n)
    : base(tok) {
    Contract.Requires(0 <= n.Mantissa.Sign);
    Contract.Requires(tok != null);
    this.Value = n;
  }

  public LiteralExpr(IToken tok, int n)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(0 <= n);
    this.Value = new BigInteger(n);
  }

  public LiteralExpr(IToken tok, bool b)
    : base(tok) {
    Contract.Requires(tok != null);
    this.Value = b;
  }

  /// <summary>
  /// This constructor is to be used only with the StringLiteralExpr and CharLiteralExpr subclasses, for
  /// two reasons:  both of these literals store a string in .Value, and string literals also carry an
  /// additional field.
  /// </summary>
  protected LiteralExpr(IToken tok, string s)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(s != null);
    this.Value = s;
  }
}

public class CharLiteralExpr : LiteralExpr {
  public CharLiteralExpr(IToken tok, string s)
    : base(tok, s) {
    Contract.Requires(s != null);
  }
}

public class StringLiteralExpr : LiteralExpr {
  public readonly bool IsVerbatim;
  public StringLiteralExpr(IToken tok, string s, bool isVerbatim)
    : base(tok, s) {
    Contract.Requires(s != null);
    IsVerbatim = isVerbatim;
  }
}

public class DatatypeValue : Expression, IHasUsages, ICloneable<DatatypeValue>, ICanFormat {
  public readonly string DatatypeName;
  public readonly string MemberName;
  public readonly ActualBindings Bindings;
  public List<Expression> Arguments => Bindings.Arguments;

  public override IEnumerable<Node> Children => new Node[] { Bindings };

  [FilledInDuringResolution] public DatatypeCtor Ctor;
  [FilledInDuringResolution] public List<Type> InferredTypeArgs = new List<Type>();
  [FilledInDuringResolution] public bool IsCoCall;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(DatatypeName != null);
    Contract.Invariant(MemberName != null);
    Contract.Invariant(cce.NonNullElements(Arguments));
    Contract.Invariant(cce.NonNullElements(InferredTypeArgs));
    Contract.Invariant(Ctor == null || InferredTypeArgs.Count == Ctor.EnclosingDatatype.TypeArgs.Count);
  }

  public DatatypeValue Clone(Cloner cloner) {
    return new DatatypeValue(cloner, this);
  }

  public DatatypeValue(Cloner cloner, DatatypeValue original) : base(cloner, original) {
    DatatypeName = original.DatatypeName;
    MemberName = original.MemberName;
    Bindings = new ActualBindings(cloner, original.Bindings);

    if (cloner.CloneResolvedFields) {
      Ctor = original.Ctor;
      IsCoCall = original.IsCoCall;
      InferredTypeArgs = original.InferredTypeArgs;
    }
  }

  public DatatypeValue(IToken tok, string datatypeName, string memberName, [Captured] List<ActualBinding> arguments)
    : base(tok) {
    Contract.Requires(cce.NonNullElements(arguments));
    Contract.Requires(tok != null);
    Contract.Requires(datatypeName != null);
    Contract.Requires(memberName != null);
    this.DatatypeName = datatypeName;
    this.MemberName = memberName;
    this.Bindings = new ActualBindings(arguments);
  }

  /// <summary>
  /// This constructor is intended to be used when constructing a resolved DatatypeValue. The "args" are expected
  /// to be already resolved, and are all given positionally.
  /// </summary>
  public DatatypeValue(IToken tok, string datatypeName, string memberName, List<Expression> arguments)
    : this(tok, datatypeName, memberName, arguments.ConvertAll(e => new ActualBinding(null, e))) {
    Bindings.AcceptArgumentExpressionsAsExactParameterList();
  }

  public override IEnumerable<Expression> SubExpressions =>
    Arguments ?? Enumerable.Empty<Expression>();

  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations() {
    return Enumerable.Repeat(Ctor, 1);
  }

  public IToken NameToken => tok;
  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    formatter.SetMethodLikeIndent(StartToken, OwnedTokens, indentBefore);
    return true;
  }
}

public class ThisExpr : Expression {
  public ThisExpr(IToken tok)
    : base(tok) {
    Contract.Requires(tok != null);
  }

  /// <summary>
  /// This constructor creates a ThisExpr and sets its Type field to denote the receiver type
  /// of member "m". This constructor is intended to be used by post-resolution code that needs
  /// to obtain a Dafny "this" expression.
  /// </summary>
  public ThisExpr(MemberDecl m)
    : base(m.tok) {
    Contract.Requires(m != null);
    Contract.Requires(m.tok != null);
    Contract.Requires(m.EnclosingClass != null);
    Contract.Requires(!m.IsStatic);
    Type = Resolver.GetReceiverType(m.tok, m);
  }

  /// <summary>
  /// This constructor creates a ThisExpr and sets its Type field to denote the receiver type
  /// of member "m". This constructor is intended to be used by post-resolution code that needs
  /// to obtain a Dafny "this" expression.
  /// </summary>
  public ThisExpr(TopLevelDeclWithMembers cl)
    : base(cl.tok) {
    Contract.Requires(cl != null);
    Contract.Requires(cl.tok != null);
    Type = Resolver.GetThisType(cl.tok, cl);
  }
}
public class ExpressionPair {
  public Expression A, B;
  public ExpressionPair(Expression a, Expression b) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    A = a;
    B = b;
  }
}

public class ImplicitThisExpr : ThisExpr {
  public ImplicitThisExpr(IToken tok)
    : base(tok) {
    Contract.Requires(tok != null);
  }

  public override bool IsImplicit {
    get { return true; }
  }
}

/// <summary>
/// An ImplicitThisExpr_ConstructorCall is used in the .InitCall of a TypeRhs,
/// which has a need for a "throw-away receiver".  Using a different type
/// gives a way to distinguish this receiver from other receivers, which
/// plays a role in checking the restrictions on divided block statements.
/// </summary>
public class ImplicitThisExpr_ConstructorCall : ImplicitThisExpr {
  public ImplicitThisExpr_ConstructorCall(IToken tok)
    : base(tok) {
    Contract.Requires(tok != null);
  }
}

public class IdentifierExpr : Expression, IHasUsages, ICloneable<IdentifierExpr> {
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Name != null);
  }

  public readonly string Name;
  [FilledInDuringResolution] public IVariable Var;

  public IdentifierExpr(IToken tok, string name)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Name = name;
  }
  /// <summary>
  /// Constructs a resolved IdentifierExpr.
  /// </summary>
  public IdentifierExpr(IToken tok, IVariable v)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(v != null);
    Name = v.Name;
    Var = v;
    Type = v.Type;
  }

  public IdentifierExpr Clone(Cloner cloner) {
    return new IdentifierExpr(cloner, this);
  }

  public IdentifierExpr(Cloner cloner, IdentifierExpr original) : base(cloner, original) {
    Name = original.Name;

    if (cloner.CloneResolvedFields) {
      Var = cloner.CloneIVariable(original.Var, true);
    }
  }

  /// <summary>
  /// Returns whether or not "expr" is an IdentifierExpr for "variable".
  /// </summary>
  public static bool Is(Expression expr, IVariable variable) {
    return expr.Resolved is IdentifierExpr identifierExpr && identifierExpr.Var == variable;
  }

  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations() {
    return Enumerable.Repeat(Var, 1);
  }

  public IToken NameToken => tok;
  public override IEnumerable<Node> Children { get; } = Enumerable.Empty<Node>();
}

/// <summary>
/// An implicit identifier is used in the context of a ReturnStmt tacetly
/// assigning a value to a Method's out parameter.
/// </summary>
public class ImplicitIdentifierExpr : IdentifierExpr {
  public ImplicitIdentifierExpr(IToken tok, string name)
    : base(tok, name) { }

  /// <summary>
  /// Constructs a resolved implicit identifier.
  /// </summary>
  public ImplicitIdentifierExpr(IToken tok, IVariable v)
    : base(tok, v) { }

  public override bool IsImplicit => true;
}


/// <summary>
/// If an "AutoGhostIdentifierExpr" is used as the out-parameter of a ghost method or
/// a method with a ghost parameter, resolution will change the .Var's .IsGhost to true
/// automatically.  This class is intended to be used only as a communicate between the
/// parser and parts of the resolver.
/// </summary>
public class AutoGhostIdentifierExpr : IdentifierExpr, ICloneable<AutoGhostIdentifierExpr> {
  public AutoGhostIdentifierExpr(IToken tok, string name)
    : base(new AutoGeneratedToken(tok), name) { }

  public AutoGhostIdentifierExpr(Cloner cloner, AutoGhostIdentifierExpr original)
    : base(cloner, original) {
  }

  public new AutoGhostIdentifierExpr Clone(Cloner cloner) {
    return new AutoGhostIdentifierExpr(cloner, this);
  }
}

/// <summary>
/// This class is used only inside the resolver itself. It gets hung in the AST in uncompleted name segments.
/// </summary>
class Resolver_IdentifierExpr : Expression, IHasUsages {
  public readonly TopLevelDecl Decl;
  public readonly List<Type> TypeArgs;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Decl != null);
    Contract.Invariant(TypeArgs != null);
    Contract.Invariant(TypeArgs.Count == Decl.TypeArgs.Count);
    Contract.Invariant(Type is ResolverType_Module || Type is ResolverType_Type);
  }

  public override IEnumerable<Node> Children => TypeArgs.SelectMany(ta => ta.Nodes);

  public abstract class ResolverType : Type {
    public override bool ComputeMayInvolveReferences(ISet<DatatypeDecl>/*?*/ visitedDatatypes) {
      return false;
    }
    public override Type Subst(IDictionary<TypeParameter, Type> subst) {
      throw new NotSupportedException();
    }

    public override Type ReplaceTypeArguments(List<Type> arguments) {
      throw new NotSupportedException();
    }
  }
  public class ResolverType_Module : ResolverType {
    [System.Diagnostics.Contracts.Pure]
    public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
      Contract.Assert(parseAble == false);
      return "#module";
    }
    public override bool Equals(Type that, bool keepConstraints = false) {
      return that.NormalizeExpand(keepConstraints) is ResolverType_Module;
    }
  }
  public class ResolverType_Type : ResolverType {
    [System.Diagnostics.Contracts.Pure]
    public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
      Contract.Assert(parseAble == false);
      return "#type";
    }
    public override bool Equals(Type that, bool keepConstraints = false) {
      return that.NormalizeExpand(keepConstraints) is ResolverType_Type;
    }
  }

  public Resolver_IdentifierExpr(IToken tok, TopLevelDecl decl, List<Type> typeArgs)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(decl != null);
    Contract.Requires(typeArgs != null && typeArgs.Count == decl.TypeArgs.Count);
    Decl = decl;
    TypeArgs = typeArgs;
    Type = decl is ModuleDecl ? (Type)new ResolverType_Module() : new ResolverType_Type();
  }
  public Resolver_IdentifierExpr(IToken tok, TypeParameter tp)
    : this(tok, tp, new List<Type>()) {
    Contract.Requires(tok != null);
    Contract.Requires(tp != null);
  }

  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations() {
    return new[] { Decl };
  }

  public IToken NameToken => tok;
}

public abstract class DisplayExpression : Expression {
  public readonly List<Expression> Elements;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Elements));
  }

  public DisplayExpression(IToken tok, List<Expression> elements)
    : base(tok) {
    Contract.Requires(cce.NonNullElements(elements));
    Elements = elements;
  }

  public override IEnumerable<Expression> SubExpressions => Elements;
}

public class SetDisplayExpr : DisplayExpression, ICanFormat {
  public bool Finite;
  public SetDisplayExpr(IToken tok, bool finite, List<Expression> elements)
    : base(tok, elements) {
    Contract.Requires(tok != null);
    Contract.Requires(cce.NonNullElements(elements));
    Finite = finite;
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentParensExpression(indentBefore, OwnedTokens);
  }
}

public class MultiSetDisplayExpr : DisplayExpression {
  public MultiSetDisplayExpr(IToken tok, List<Expression> elements) : base(tok, elements) {
    Contract.Requires(tok != null);
    Contract.Requires(cce.NonNullElements(elements));
  }
}

public class MapDisplayExpr : Expression, ICanFormat {
  public bool Finite;
  public List<ExpressionPair> Elements;
  public MapDisplayExpr(IToken tok, bool finite, List<ExpressionPair> elements)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(cce.NonNullElements(elements));
    Finite = finite;
    Elements = elements;
  }
  public override IEnumerable<Expression> SubExpressions {
    get {
      foreach (var ep in Elements) {
        yield return ep.A;
        yield return ep.B;
      }
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentParensExpression(indentBefore, OwnedTokens);
  }
}
public class SeqDisplayExpr : DisplayExpression, ICanFormat {
  public SeqDisplayExpr(IToken tok, List<Expression> elements)
    : base(tok, elements) {
    Contract.Requires(cce.NonNullElements(elements));
    Contract.Requires(tok != null);
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentParensExpression(indentBefore, OwnedTokens);
  }
}

public class SeqSelectExpr : Expression {
  public readonly bool SelectOne;  // false means select a range
  public readonly Expression Seq;
  public readonly Expression E0;
  public readonly Expression E1;
  public readonly IToken CloseParen;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Seq != null);
    Contract.Invariant(!SelectOne || E1 == null);
  }

  public SeqSelectExpr(IToken tok, bool selectOne, Expression seq, Expression e0, Expression e1, IToken closeParen)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(seq != null);
    Contract.Requires(!selectOne || e1 == null);

    SelectOne = selectOne;
    Seq = seq;
    E0 = e0;
    E1 = e1;
    CloseParen = closeParen;
    if (closeParen != null) {
      FormatTokens = new[] { closeParen };
    }
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return Seq;
      if (E0 != null) {
        yield return E0;
      }

      if (E1 != null) {
        yield return E1;
      }
    }
  }
}

public class MultiSelectExpr : Expression {
  public readonly Expression Array;
  public readonly List<Expression> Indices;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Array != null);
    Contract.Invariant(cce.NonNullElements(Indices));
    Contract.Invariant(1 <= Indices.Count);
  }

  public MultiSelectExpr(IToken tok, Expression array, List<Expression> indices)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(array != null);
    Contract.Requires(cce.NonNullElements(indices) && 1 <= indices.Count);

    Array = array;
    Indices = indices;
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return Array;
      foreach (var e in Indices) {
        yield return e;
      }
    }
  }
}

/// <summary>
/// Represents an expression of the form S[I := V], where, syntactically, S, I, and V are expressions.
///
/// Successfully resolved, the expression stands for one of the following:
/// * if S is a seq<T>, then I is an integer-based index into the sequence and V is of type T
/// * if S is a map<T, U>, then I is a key of type T and V is a value of type U
/// * if S is a multiset<T>, then I is an element of type T and V has an integer-based numeric type.
///
/// Datatype updates are represented by <c>DatatypeUpdateExpr</c> nodes.
/// </summary>
public class SeqUpdateExpr : Expression {
  public readonly Expression Seq;
  public readonly Expression Index;
  public readonly Expression Value;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Seq != null);
    Contract.Invariant(Index != null);
    Contract.Invariant(Value != null);
  }

  public SeqUpdateExpr(IToken tok, Expression seq, Expression index, Expression val)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(seq != null);
    Contract.Requires(index != null);
    Contract.Requires(val != null);
    Seq = seq;
    Index = index;
    Value = val;
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return Seq;
      yield return Index;
      yield return Value;
    }
  }
}

public class ApplyExpr : Expression {
  // The idea is that this apply expression does not need a type argument substitution,
  // since lambda functions and anonymous functions are never polymorphic.
  // Make a FunctionCallExpr otherwise, to call a resolvable anonymous function.
  public readonly Expression Function;
  public readonly List<Expression> Args;

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return Function;
      foreach (var e in Args) {
        yield return e;
      }
    }
  }

  public IToken CloseParen;

  public ApplyExpr(IToken tok, Expression fn, List<Expression> args, IToken closeParen)
    : base(tok) {
    Function = fn;
    Args = args;
    CloseParen = closeParen;
    FormatTokens = closeParen != null ? new[] { closeParen } : null;
  }
}

public class FunctionCallExpr : Expression, IHasUsages, ICloneable<FunctionCallExpr> {
  public string Name;
  public readonly Expression Receiver;
  public readonly IToken OpenParen;  // can be null if Args.Count == 0
  public readonly IToken CloseParen;
  public readonly Label/*?*/ AtLabel;
  public readonly ActualBindings Bindings;
  public List<Expression> Args => Bindings.Arguments;
  [FilledInDuringResolution] public List<Type> TypeApplication_AtEnclosingClass;
  [FilledInDuringResolution] public List<Type> TypeApplication_JustFunction;
  [FilledInDuringResolution] public bool IsByMethodCall;

  /// <summary>
  /// Return a mapping from each type parameter of the function and its enclosing class to actual type arguments.
  /// This method should only be called on fully and successfully resolved FunctionCallExpr's.
  /// </summary>
  public Dictionary<TypeParameter, Type> GetTypeArgumentSubstitutions() {
    var typeMap = new Dictionary<TypeParameter, Type>();
    Util.AddToDict(typeMap, Function.EnclosingClass.TypeArgs, TypeApplication_AtEnclosingClass);
    Util.AddToDict(typeMap, Function.TypeArgs, TypeApplication_JustFunction);
    return typeMap;
  }

  /// <summary>
  /// Returns a mapping from formal type parameters to actual type arguments. For example, given
  ///     trait T<A> {
  ///       function F<X>(): bv8 { ... }
  ///     }
  ///     class C<B, D> extends T<map<B, D>> { }
  /// and FunctionCallExpr o.F<int>(args) where o has type C<real, bool>, the type map returned is
  ///     A -> map<real, bool>
  ///     B -> real
  ///     D -> bool
  ///     X -> int
  /// NOTE: This method should be called only when all types have been fully and successfully
  /// resolved.
  /// </summary>
  public Dictionary<TypeParameter, Type> TypeArgumentSubstitutionsWithParents() {
    Contract.Requires(WasResolved());
    Contract.Ensures(Contract.Result<Dictionary<TypeParameter, Type>>() != null);

    return MemberSelectExpr.TypeArgumentSubstitutionsWithParentsAux(Receiver.Type, Function, TypeApplication_JustFunction);
  }

  public enum CoCallResolution {
    No,
    Yes,
    NoBecauseFunctionHasSideEffects,
    NoBecauseFunctionHasPostcondition,
    NoBecauseRecursiveCallsAreNotAllowedInThisContext,
    NoBecauseIsNotGuarded,
    NoBecauseRecursiveCallsInDestructiveContext
  }
  [FilledInDuringResolution] public CoCallResolution CoCall = CoCallResolution.No;  // indicates whether or not the call is a co-recursive call
  [FilledInDuringResolution] public string CoCallHint = null;  // possible additional hint that can be used in verifier error message

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Name != null);
    Contract.Invariant(Receiver != null);
    Contract.Invariant(cce.NonNullElements(Args));
    Contract.Invariant(
      Function == null || TypeApplication_AtEnclosingClass == null ||
      Function.EnclosingClass.TypeArgs.Count == TypeApplication_AtEnclosingClass.Count);
    Contract.Invariant(
      Function == null || TypeApplication_JustFunction == null ||
      Function.TypeArgs.Count == TypeApplication_JustFunction.Count);
  }

  [FilledInDuringResolution] public Function Function;

  public FunctionCallExpr(IToken tok, string fn, Expression receiver, IToken openParen, IToken closeParen, [Captured] List<ActualBinding> args, Label/*?*/ atLabel = null)
    : this(tok, fn, receiver, openParen, closeParen, new ActualBindings(args), atLabel) {
    Contract.Requires(tok != null);
    Contract.Requires(fn != null);
    Contract.Requires(receiver != null);
    Contract.Requires(cce.NonNullElements(args));
    Contract.Requires(openParen != null || args.Count == 0);
    Contract.Ensures(type == null);
  }

  public FunctionCallExpr(IToken tok, string fn, Expression receiver, IToken openParen, IToken closeParen, [Captured] ActualBindings bindings, Label/*?*/ atLabel = null)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(fn != null);
    Contract.Requires(receiver != null);
    Contract.Requires(bindings != null);
    Contract.Requires(openParen != null);
    Contract.Ensures(type == null);

    this.Name = fn;
    this.Receiver = receiver;
    this.OpenParen = openParen;
    this.CloseParen = closeParen;
    this.AtLabel = atLabel;
    this.Bindings = bindings;
    this.FormatTokens = closeParen != null ? new[] { closeParen } : null;
  }

  /// <summary>
  /// This constructor is intended to be used when constructing a resolved FunctionCallExpr. The "args" are expected
  /// to be already resolved, and are all given positionally.
  /// </summary>
  public FunctionCallExpr(IToken tok, string fn, Expression receiver, IToken openParen, IToken closeParen, [Captured] List<Expression> args,
    Label /*?*/ atLabel = null)
    : this(tok, fn, receiver, openParen, closeParen, args.ConvertAll(e => new ActualBinding(null, e)), atLabel) {
    Bindings.AcceptArgumentExpressionsAsExactParameterList();
  }

  public FunctionCallExpr Clone(Cloner cloner) {
    return new FunctionCallExpr(cloner, this);
  }

  public FunctionCallExpr(Cloner cloner, FunctionCallExpr original) : base(cloner, original) {
    Name = original.Name;
    Receiver = cloner.CloneExpr(original.Receiver);
    OpenParen = original.OpenParen == null ? null : cloner.Tok(original.OpenParen);
    CloseParen = original.CloseParen == null ? null : cloner.Tok(original.CloseParen);
    Bindings = new ActualBindings(cloner, original.Bindings);
    AtLabel = original.AtLabel;

    if (cloner.CloneResolvedFields) {
      TypeApplication_AtEnclosingClass = original.TypeApplication_AtEnclosingClass;
      TypeApplication_JustFunction = original.TypeApplication_JustFunction;
      IsByMethodCall = original.IsByMethodCall;
      Function = original.Function;
      CoCall = original.CoCall;
      CoCallHint = original.CoCallHint;
    }
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return Receiver;
      foreach (var e in Args) {
        yield return e;
      }
    }
  }

  public override IEnumerable<Type> ComponentTypes => Util.Concat(TypeApplication_AtEnclosingClass, TypeApplication_JustFunction);
  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations() {
    return Enumerable.Repeat(Function, 1);
  }

  public IToken NameToken => tok;
}

public class SeqConstructionExpr : Expression {
  public Type/*?*/ ExplicitElementType;
  public Expression N;
  public Expression Initializer;
  public SeqConstructionExpr(IToken tok, Type/*?*/ elementType, Expression length, Expression initializer)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(length != null);
    Contract.Requires(initializer != null);
    ExplicitElementType = elementType;
    N = length;
    Initializer = initializer;
  }
  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return N;
      yield return Initializer;
    }
  }

  public override IEnumerable<Type> ComponentTypes {
    get {
      if (ExplicitElementType != null) {
        yield return ExplicitElementType;
      }
    }
  }
}

public class MultiSetFormingExpr : Expression {
  [Peer]
  public readonly Expression E;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(E != null);
  }

  [Captured]
  public MultiSetFormingExpr(IToken tok, Expression expr)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(expr != null);
    cce.Owner.AssignSame(this, expr);
    E = expr;
  }

  public override IEnumerable<Expression> SubExpressions {
    get { yield return E; }
  }
}

public abstract class UnaryExpr : Expression, ICanFormat {
  public readonly Expression E;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(E != null);
  }

  public UnaryExpr(IToken tok, Expression e)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(e != null);
    this.E = e;
  }

  public UnaryExpr(Cloner cloner, UnaryExpr original) : base(cloner, original) {
    E = cloner.CloneExpr(original.E);
  }

  public override IEnumerable<Expression> SubExpressions {
    get { yield return E; }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentParensExpression(indentBefore, OwnedTokens);
  }
}

public class UnaryOpExpr : UnaryExpr {
  public enum Opcode {
    Not,  // boolean negation or bitwise negation
    Cardinality,
    Fresh, // fresh also has a(n optional) second argument, namely the @-label
    Allocated,
    Lit,  // there is no syntax for this operator, but it is sometimes introduced during translation
  }
  public readonly Opcode Op;

  public enum ResolvedOpcode {
    YetUndetermined,
    BVNot,
    BoolNot,
    SeqLength,
    SetCard,
    MultiSetCard,
    MapCard,
    Fresh,
    Allocated,
    Lit
  }

  private ResolvedOpcode _ResolvedOp = ResolvedOpcode.YetUndetermined;
  public ResolvedOpcode ResolvedOp => ResolveOp();

  public ResolvedOpcode ResolveOp() {
    if (_ResolvedOp == ResolvedOpcode.YetUndetermined) {
      Contract.Assert(Type != null);
      Contract.Assert(Type is not TypeProxy);
      _ResolvedOp = (Op, E.Type.NormalizeExpand()) switch {
        (Opcode.Not, BoolType _) => ResolvedOpcode.BoolNot,
        (Opcode.Not, BitvectorType _) => ResolvedOpcode.BVNot,
        (Opcode.Cardinality, SeqType _) => ResolvedOpcode.SeqLength,
        (Opcode.Cardinality, SetType _) => ResolvedOpcode.SetCard,
        (Opcode.Cardinality, MultiSetType _) => ResolvedOpcode.MultiSetCard,
        (Opcode.Cardinality, MapType _) => ResolvedOpcode.MapCard,
        (Opcode.Fresh, _) => ResolvedOpcode.Fresh,
        (Opcode.Allocated, _) => ResolvedOpcode.Allocated,
        (Opcode.Lit, _) => ResolvedOpcode.Lit,
        _ => ResolvedOpcode.YetUndetermined // Unreachable
      };
      Contract.Assert(_ResolvedOp != ResolvedOpcode.YetUndetermined);
    }

    return _ResolvedOp;
  }

  public UnaryOpExpr(IToken tok, Opcode op, Expression e)
    : base(tok, e) {
    Contract.Requires(tok != null);
    Contract.Requires(e != null);
    Contract.Requires(op != Opcode.Fresh || this is FreshExpr);
    this.Op = op;
  }

  public UnaryOpExpr(Cloner cloner, UnaryOpExpr original) : base(cloner, original) {
    Op = original.Op;
  }

  public override bool IsImplicit => Op == Opcode.Lit;
}

public class FreshExpr : UnaryOpExpr, ICloneable<FreshExpr> {
  public readonly string/*?*/ At;
  [FilledInDuringResolution] public Label/*?*/ AtLabel;  // after that, At==null iff AtLabel==null

  public FreshExpr(IToken tok, Expression e, string at = null)
    : base(tok, Opcode.Fresh, e) {
    Contract.Requires(tok != null);
    Contract.Requires(e != null);
    this.At = at;
  }

  public FreshExpr(Cloner cloner, FreshExpr original) : base(cloner, original) {
    At = original.At;
    if (cloner.CloneResolvedFields) {
      AtLabel = original.AtLabel;
    }
  }

  public FreshExpr Clone(Cloner cloner) { return new FreshExpr(cloner, this); }
}

public abstract class TypeUnaryExpr : UnaryExpr {
  public readonly Type ToType;
  public TypeUnaryExpr(IToken tok, Expression expr, Type toType)
    : base(tok, expr) {
    Contract.Requires(tok != null);
    Contract.Requires(expr != null);
    Contract.Requires(toType != null);
    ToType = toType;
  }

  public override IEnumerable<Node> Children => base.Children.Concat(ToType.Nodes);

  public override IEnumerable<Type> ComponentTypes {
    get {
      yield return ToType;
    }
  }
}

public class ConversionExpr : TypeUnaryExpr {
  public readonly string messagePrefix;
  public ConversionExpr(IToken tok, Expression expr, Type toType, string messagePrefix = "")
    : base(tok, expr, toType) {
    Contract.Requires(tok != null);
    Contract.Requires(expr != null);
    Contract.Requires(toType != null);
    this.messagePrefix = messagePrefix;
  }
}

public class TypeTestExpr : TypeUnaryExpr {
  public TypeTestExpr(IToken tok, Expression expr, Type toType)
    : base(tok, expr, toType) {
    Contract.Requires(tok != null);
    Contract.Requires(expr != null);
    Contract.Requires(toType != null);
  }
}

public class BinaryExpr : Expression, ICloneable<BinaryExpr>, ICanFormat {
  public enum Opcode {
    Iff,
    Imp,
    Exp, // turned into Imp during resolution
    And,
    Or,
    Eq,
    Neq,
    Lt,
    Le,
    Ge,
    Gt,
    Disjoint,
    In,
    NotIn,
    LeftShift,
    RightShift,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor
  }
  public readonly Opcode Op;
  public enum ResolvedOpcode {
    YetUndetermined,  // the value before resolution has determined the value; .ResolvedOp should never be read in this state

    // logical operators
    Iff,
    Imp,
    And,
    Or,
    // non-collection types
    EqCommon,
    NeqCommon,
    // integers, reals, bitvectors
    Lt,
    LessThanLimit,  // a synonym for Lt for ORDINAL, used only during translation
    Le,
    Ge,
    Gt,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    // bitvectors
    LeftShift,
    RightShift,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    // char
    LtChar,
    LeChar,
    GeChar,
    GtChar,
    // sets
    SetEq,
    SetNeq,
    ProperSubset,
    Subset,
    Superset,
    ProperSuperset,
    Disjoint,
    InSet,
    NotInSet,
    Union,
    Intersection,
    SetDifference,
    // multi-sets
    MultiSetEq,
    MultiSetNeq,
    MultiSubset,
    MultiSuperset,
    ProperMultiSubset,
    ProperMultiSuperset,
    MultiSetDisjoint,
    InMultiSet,
    NotInMultiSet,
    MultiSetUnion,
    MultiSetIntersection,
    MultiSetDifference,
    // Sequences
    SeqEq,
    SeqNeq,
    ProperPrefix,
    Prefix,
    Concat,
    InSeq,
    NotInSeq,
    // Maps
    MapEq,
    MapNeq,
    InMap,
    NotInMap,
    MapMerge,
    MapSubtraction,
    // datatypes
    RankLt,
    RankGt
  }
  private ResolvedOpcode _theResolvedOp = ResolvedOpcode.YetUndetermined;
  public ResolvedOpcode ResolvedOp {
    set {
      Contract.Assume(_theResolvedOp == ResolvedOpcode.YetUndetermined || _theResolvedOp == value);  // there's never a reason for resolution to change its mind, is there?
      _theResolvedOp = value;
    }
    get {
      Debug.Assert(_theResolvedOp != ResolvedOpcode.YetUndetermined);  // shouldn't read it until it has been properly initialized
      return _theResolvedOp;
    }
  }
  public ResolvedOpcode ResolvedOp_PossiblyStillUndetermined {  // offer a way to return _theResolveOp -- for experts only!
    get { return _theResolvedOp; }
  }
  public static bool IsEqualityOp(ResolvedOpcode op) {
    switch (op) {
      case ResolvedOpcode.EqCommon:
      case ResolvedOpcode.SetEq:
      case ResolvedOpcode.SeqEq:
      case ResolvedOpcode.MultiSetEq:
      case ResolvedOpcode.MapEq:
        return true;
      default:
        return false;
    }
  }

  public static Opcode ResolvedOp2SyntacticOp(ResolvedOpcode rop) {
    switch (rop) {
      case ResolvedOpcode.Iff: return Opcode.Iff;
      case ResolvedOpcode.Imp: return Opcode.Imp;
      case ResolvedOpcode.And: return Opcode.And;
      case ResolvedOpcode.Or: return Opcode.Or;

      case ResolvedOpcode.EqCommon:
      case ResolvedOpcode.SetEq:
      case ResolvedOpcode.MultiSetEq:
      case ResolvedOpcode.SeqEq:
      case ResolvedOpcode.MapEq:
        return Opcode.Eq;

      case ResolvedOpcode.NeqCommon:
      case ResolvedOpcode.SetNeq:
      case ResolvedOpcode.MultiSetNeq:
      case ResolvedOpcode.SeqNeq:
      case ResolvedOpcode.MapNeq:
        return Opcode.Neq;

      case ResolvedOpcode.Lt:
      case ResolvedOpcode.LtChar:
      case ResolvedOpcode.ProperSubset:
      case ResolvedOpcode.ProperMultiSuperset:
      case ResolvedOpcode.ProperPrefix:
      case ResolvedOpcode.RankLt:
        return Opcode.Lt;

      case ResolvedOpcode.Le:
      case ResolvedOpcode.LeChar:
      case ResolvedOpcode.Subset:
      case ResolvedOpcode.MultiSubset:
      case ResolvedOpcode.Prefix:
        return Opcode.Le;

      case ResolvedOpcode.Ge:
      case ResolvedOpcode.GeChar:
      case ResolvedOpcode.Superset:
      case ResolvedOpcode.MultiSuperset:
        return Opcode.Ge;

      case ResolvedOpcode.Gt:
      case ResolvedOpcode.GtChar:
      case ResolvedOpcode.ProperSuperset:
      case ResolvedOpcode.ProperMultiSubset:
      case ResolvedOpcode.RankGt:
        return Opcode.Gt;

      case ResolvedOpcode.LeftShift:
        return Opcode.LeftShift;

      case ResolvedOpcode.RightShift:
        return Opcode.RightShift;

      case ResolvedOpcode.Add:
      case ResolvedOpcode.Union:
      case ResolvedOpcode.MultiSetUnion:
      case ResolvedOpcode.MapMerge:
      case ResolvedOpcode.Concat:
        return Opcode.Add;

      case ResolvedOpcode.Sub:
      case ResolvedOpcode.SetDifference:
      case ResolvedOpcode.MultiSetDifference:
      case ResolvedOpcode.MapSubtraction:
        return Opcode.Sub;

      case ResolvedOpcode.Mul:
      case ResolvedOpcode.Intersection:
      case ResolvedOpcode.MultiSetIntersection:
        return Opcode.Mul;

      case ResolvedOpcode.Div: return Opcode.Div;
      case ResolvedOpcode.Mod: return Opcode.Mod;

      case ResolvedOpcode.BitwiseAnd: return Opcode.BitwiseAnd;
      case ResolvedOpcode.BitwiseOr: return Opcode.BitwiseOr;
      case ResolvedOpcode.BitwiseXor: return Opcode.BitwiseXor;

      case ResolvedOpcode.Disjoint:
      case ResolvedOpcode.MultiSetDisjoint:
        return Opcode.Disjoint;

      case ResolvedOpcode.InSet:
      case ResolvedOpcode.InMultiSet:
      case ResolvedOpcode.InSeq:
      case ResolvedOpcode.InMap:
        return Opcode.In;

      case ResolvedOpcode.NotInSet:
      case ResolvedOpcode.NotInMultiSet:
      case ResolvedOpcode.NotInSeq:
      case ResolvedOpcode.NotInMap:
        return Opcode.NotIn;

      case ResolvedOpcode.LessThanLimit:  // not expected here (but if it were, the same case as Lt could perhaps be used)
      default:
        Contract.Assert(false);  // unexpected ResolvedOpcode
        return Opcode.Add;  // please compiler
    }
  }

  public static string OpcodeString(Opcode op) {
    Contract.Ensures(Contract.Result<string>() != null);

    switch (op) {
      case Opcode.Iff:
        return "<==>";
      case Opcode.Imp:
        return "==>";
      case Opcode.Exp:
        return "<==";
      case Opcode.And:
        return "&&";
      case Opcode.Or:
        return "||";
      case Opcode.Eq:
        return "==";
      case Opcode.Lt:
        return "<";
      case Opcode.Gt:
        return ">";
      case Opcode.Le:
        return "<=";
      case Opcode.Ge:
        return ">=";
      case Opcode.Neq:
        return "!=";
      case Opcode.Disjoint:
        return "!!";
      case Opcode.In:
        return "in";
      case Opcode.NotIn:
        return "!in";
      case Opcode.LeftShift:
        return "<<";
      case Opcode.RightShift:
        return ">>";
      case Opcode.Add:
        return "+";
      case Opcode.Sub:
        return "-";
      case Opcode.Mul:
        return "*";
      case Opcode.Div:
        return "/";
      case Opcode.Mod:
        return "%";
      case Opcode.BitwiseAnd:
        return "&";
      case Opcode.BitwiseOr:
        return "|";
      case Opcode.BitwiseXor:
        return "^";
      default:
        Contract.Assert(false);
        throw new cce.UnreachableException();  // unexpected operator
    }
  }
  public Expression E0;
  public Expression E1;
  public enum AccumulationOperand { None, Left, Right }
  public AccumulationOperand AccumulatesForTailRecursion = AccumulationOperand.None; // set by Resolver
  [FilledInDuringResolution] public bool InCompiledContext;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(E0 != null);
    Contract.Invariant(E1 != null);
  }

  public BinaryExpr Clone(Cloner cloner) {
    return new BinaryExpr(cloner, this);
  }

  public BinaryExpr(Cloner cloner, BinaryExpr original) : base(cloner, original) {
    this.Op = original.Op;
    this.E0 = cloner.CloneExpr(original.E0);
    this.E1 = cloner.CloneExpr(original.E1);

    if (cloner.CloneResolvedFields) {
      ResolvedOp = original.ResolvedOp;
    }
  }

  public BinaryExpr(IToken tok, Opcode op, Expression e0, Expression e1)
    :
    base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(e0 != null);
    Contract.Requires(e1 != null);
    this.Op = op;
    this.E0 = e0;
    this.E1 = e1;
  }

  /// <summary>
  /// Returns a resolved binary expression
  /// </summary>
  public BinaryExpr(IToken tok, BinaryExpr.ResolvedOpcode rop, Expression e0, Expression e1)
    : this(tok, BinaryExpr.ResolvedOp2SyntacticOp(rop), e0, e1) {
    ResolvedOp = rop;
    switch (rop) {
      case ResolvedOpcode.EqCommon:
      case ResolvedOpcode.NeqCommon:
      case ResolvedOpcode.Lt:
      case ResolvedOpcode.LessThanLimit:
      case ResolvedOpcode.Le:
      case ResolvedOpcode.Ge:
      case ResolvedOpcode.Gt:
      case ResolvedOpcode.LtChar:
      case ResolvedOpcode.LeChar:
      case ResolvedOpcode.GeChar:
      case ResolvedOpcode.GtChar:
      case ResolvedOpcode.SetEq:
      case ResolvedOpcode.SetNeq:
      case ResolvedOpcode.ProperSubset:
      case ResolvedOpcode.Subset:
      case ResolvedOpcode.Superset:
      case ResolvedOpcode.ProperSuperset:
      case ResolvedOpcode.Disjoint:
      case ResolvedOpcode.InSet:
      case ResolvedOpcode.NotInSet:
      case ResolvedOpcode.MultiSetEq:
      case ResolvedOpcode.MultiSetNeq:
      case ResolvedOpcode.MultiSubset:
      case ResolvedOpcode.MultiSuperset:
      case ResolvedOpcode.ProperMultiSubset:
      case ResolvedOpcode.ProperMultiSuperset:
      case ResolvedOpcode.MultiSetDisjoint:
      case ResolvedOpcode.InMultiSet:
      case ResolvedOpcode.NotInMultiSet:
      case ResolvedOpcode.SeqEq:
      case ResolvedOpcode.SeqNeq:
      case ResolvedOpcode.ProperPrefix:
      case ResolvedOpcode.Prefix:
      case ResolvedOpcode.InSeq:
      case ResolvedOpcode.NotInSeq:
      case ResolvedOpcode.MapEq:
      case ResolvedOpcode.MapNeq:
      case ResolvedOpcode.InMap:
      case ResolvedOpcode.NotInMap:
      case ResolvedOpcode.RankLt:
      case ResolvedOpcode.RankGt:
        Type = Type.Bool;
        break;
      default:
        Type = e0.Type;
        break;
    }
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return E0;
      yield return E1;
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    var indent = indentBefore;
    if (Op is Opcode.And or Opcode.Or) {
      var ownedTokens = OwnedTokens.ToList();
      // Alignment required.
      if (ownedTokens.Count == 2) {
        var firstToken = ownedTokens[0];
        var secondToken = ownedTokens[1];
        indent = formatter.GetNewTokenVisualIndent(firstToken, formatter.GetIndentInlineOrAbove(firstToken));
        var c = 0;
        while (c < firstToken.TrailingTrivia.Length && firstToken.TrailingTrivia[c] == ' ') {
          c++;
        }

        var conjunctExtraIndent = c + formatter.SpaceTab;
        formatter.binOpIndent = indent;
        formatter.binOpArgIndent = indent + conjunctExtraIndent;
        formatter.SetIndentations(firstToken, formatter.binOpIndent, formatter.binOpIndent, formatter.binOpArgIndent);
        formatter.SetIndentations(secondToken, formatter.binOpIndent, formatter.binOpIndent, formatter.binOpArgIndent);
      } else if (ownedTokens.Count > 0) {
        if (ownedTokens[0].val == "requires") { // Requirement conjunctions inside lambdas are separated by the keyword "requires"
          if (this.StartToken.Prev.val == "requires") {
            formatter.binOpIndent = formatter.GetIndentInlineOrAbove(this.StartToken.Prev);
          }
        }
        if (formatter.binOpIndent > 0) {
          formatter.SetIndentations(ownedTokens[0], formatter.binOpIndent, formatter.binOpIndent, formatter.binOpArgIndent);
        } else {
          var startToken = this.StartToken;
          var newIndent = formatter.GetNewTokenVisualIndent(startToken, formatter.GetIndentInlineOrAbove(startToken));
          formatter.SetIndentations(ownedTokens[0], newIndent, newIndent, newIndent);
        }
      }

      if (formatter.binOpIndent > 0 && (this.E0 is not BinaryExpr { Op: var op } || op != this.Op)) {
        formatter.binOpIndent = -1;
        formatter.binOpArgIndent = -1;
      }

      return true; // Default indentation
    } else if (Op is Opcode.Imp or Opcode.Exp) {
      foreach (var token in this.OwnedTokens) {
        switch (token.val) {
          case "==>": {
              formatter.SetOpeningIndentedRegion(token, indent);
              break;
            }
          case "<==": {
              formatter.SetIndentations(token, indent, indent, indent);
              break;
            }
        }
      }
      formatter.Visit(this.E0, indent);
      formatter.Visit(this.E1, this.Op is BinaryExpr.Opcode.Exp ? indent : indent + formatter.SpaceTab);
      formatter.SetIndentations(this.EndToken, below: indent);
      return false;
    } else if (Op is Opcode.Eq or Opcode.Le or Opcode.Lt or Opcode.Ge or Opcode.Gt or Opcode.Iff or Opcode.Neq) {
      var itemIndent = formatter.GetNewTokenVisualIndent(
          E0.StartToken, indent);
      var item2Indent = itemIndent;
      var startToken = this.E0.StartToken;
      if (startToken.Prev.line == startToken.line) {
        // like assert E0
        //          == E1
        // Careful: The binaryExpr.op's first column should be greater than the
        // token's first column before E0.StartToken. 
        foreach (var token in this.OwnedTokens) {
          switch (token.val) {
            case "==":
            case "<=":
            case "<":
            case ">=":
            case ">":
            case "<==>":
            case "!=": {
                var followedByNewline = TokenNewIndentCollector.IsFollowedByNewline(token);
                var selfIndent = followedByNewline ? itemIndent : Math.Max(itemIndent - token.val.Length - 1, 0);
                if (selfIndent <= formatter.GetNewTokenVisualIndent(startToken.Prev, itemIndent)) {
                  // There could be a visual ambiguity if this token is aligned with the enclosing token.
                  selfIndent = itemIndent;
                }
                formatter.SetIndentations(token, itemIndent, selfIndent);
                item2Indent = followedByNewline ? itemIndent : formatter.GetNewTokenVisualIndent(this.E1.StartToken, itemIndent);
                formatter.SetIndentations(token, below: item2Indent);
                break;
              }
          }
        }
      }
      formatter.Visit(E0, itemIndent);
      formatter.Visit(E1, item2Indent);
      formatter.SetIndentations(EndToken, below: indent);
      return false;
    } else {
      foreach (var token in OwnedTokens) {
        formatter.SetIndentations(token, indent, indent, indent);
      }
      formatter.Visit(E0, indent);
      formatter.Visit(E1, indent);
      formatter.SetIndentations(EndToken, below: indent);
      return false;
    }
  }
}

public class TernaryExpr : Expression {
  public readonly Opcode Op;
  public readonly Expression E0;
  public readonly Expression E1;
  public readonly Expression E2;
  public enum Opcode { /*SOON: IfOp,*/ PrefixEqOp, PrefixNeqOp }
  public static readonly bool PrefixEqUsesNat = false;  // "k" is either a "nat" or an "ORDINAL"
  public TernaryExpr(IToken tok, Opcode op, Expression e0, Expression e1, Expression e2)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(e0 != null);
    Contract.Requires(e1 != null);
    Contract.Requires(e2 != null);
    Op = op;
    E0 = e0;
    E1 = e1;
    E2 = e2;
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return E0;
      yield return E1;
      yield return E2;
    }
  }
}

public class LetOrFailExpr : ConcreteSyntaxExpression, ICloneable<LetOrFailExpr>, ICanFormat {
  public readonly CasePattern<BoundVar>/*?*/ Lhs; // null means void-error handling: ":- E; F", non-null means "var pat :- E; F"
  public readonly Expression Rhs;
  public readonly Expression Body;

  public LetOrFailExpr(IToken tok, CasePattern<BoundVar>/*?*/ lhs, Expression rhs, Expression body) : base(tok) {
    Lhs = lhs;
    Rhs = rhs;
    Body = body;
  }

  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      yield return Rhs;
      yield return Body;
    }
  }

  public LetOrFailExpr Clone(Cloner cloner) {
    return new LetOrFailExpr(cloner, this);
  }

  public LetOrFailExpr(Cloner cloner, LetOrFailExpr original) : base(cloner, original) {
    Lhs = original.Lhs == null ? null : cloner.CloneCasePattern(original.Lhs);
    Rhs = cloner.CloneExpr(original.Rhs);
    Body = cloner.CloneExpr(original.Body);
  }

  public override IEnumerable<Node> Children =>
    (Lhs != null ?
    new List<Node> { Lhs } : Enumerable.Empty<Node>()).Concat(base.Children);

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentVarDeclStmt(indentBefore, OwnedTokens, Lhs == null, true);
  }
}

public class ForallExpr : QuantifierExpr, ICloneable<ForallExpr> {
  public override string WhatKind => "forall expression";
  protected override BinaryExpr.ResolvedOpcode SplitResolvedOp { get { return BinaryExpr.ResolvedOpcode.And; } }

  public ForallExpr(IToken tok, RangeToken rangeToken, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
    : base(tok, rangeToken, bvars, range, term, attrs) {
    Contract.Requires(cce.NonNullElements(bvars));
    Contract.Requires(tok != null);
    Contract.Requires(term != null);
  }

  public ForallExpr Clone(Cloner cloner) {
    return new ForallExpr(cloner, this);
  }

  public ForallExpr(Cloner cloner, ForallExpr original) : base(cloner, original) {
  }

  public override Expression LogicalBody(bool bypassSplitQuantifier = false) {
    if (Range == null) {
      return Term;
    }
    var body = new BinaryExpr(Term.tok, BinaryExpr.Opcode.Imp, Range, Term);
    body.ResolvedOp = BinaryExpr.ResolvedOpcode.Imp;
    body.Type = Term.Type;
    return body;
  }
}

public class ExistsExpr : QuantifierExpr, ICloneable<ExistsExpr> {
  public override string WhatKind => "exists expression";
  protected override BinaryExpr.ResolvedOpcode SplitResolvedOp { get { return BinaryExpr.ResolvedOpcode.Or; } }

  public ExistsExpr(IToken tok, RangeToken rangeToken, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
    : base(tok, rangeToken, bvars, range, term, attrs) {
    Contract.Requires(cce.NonNullElements(bvars));
    Contract.Requires(tok != null);
    Contract.Requires(term != null);
  }

  public ExistsExpr Clone(Cloner cloner) {
    return new ExistsExpr(cloner, this);
  }

  public ExistsExpr(Cloner cloner, ExistsExpr existsExpr) : base(cloner, existsExpr) {
  }

  public override Expression LogicalBody(bool bypassSplitQuantifier = false) {
    if (Range == null) {
      return Term;
    }
    var body = new BinaryExpr(Term.tok, BinaryExpr.Opcode.And, Range, Term);
    body.ResolvedOp = BinaryExpr.ResolvedOpcode.And;
    body.Type = Term.Type;
    return body;
  }
}

public class SetComprehension : ComprehensionExpr, ICloneable<SetComprehension> {
  public override string WhatKind => "set comprehension";

  public readonly bool Finite;
  public readonly bool TermIsImplicit;  // records the given syntactic form
  public bool TermIsSimple {
    get {
      var term = Term as IdentifierExpr;
      var r = term != null && BoundVars.Count == 1 && BoundVars[0].Name == term.Name;
      Contract.Assert(!TermIsImplicit || r);  // TermIsImplicit ==> r
      Contract.Assert(!r || term.Var == null || term.Var == BoundVars[0]);  // if the term is simple and it has been resolved, then it should have resolved to BoundVars[0]
      return r;
    }
  }

  public SetComprehension Clone(Cloner cloner) {
    return new SetComprehension(cloner, this);
  }

  public SetComprehension(Cloner cloner, SetComprehension original) : base(cloner, original) {
    TermIsImplicit = original.TermIsImplicit;
    Finite = original.Finite;
  }

  public SetComprehension(IToken tok, RangeToken rangeToken, bool finite, List<BoundVar> bvars, Expression range, Expression/*?*/ term, Attributes attrs)
    : base(tok, rangeToken, bvars, range, term ?? new IdentifierExpr(tok, bvars[0].Name), attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(cce.NonNullElements(bvars));
    Contract.Requires(1 <= bvars.Count);
    Contract.Requires(range != null);
    Contract.Requires(term != null || bvars.Count == 1);

    TermIsImplicit = term == null;
    Finite = finite;
  }
}
public class MapComprehension : ComprehensionExpr, ICloneable<MapComprehension> {
  public override string WhatKind => "map comprehension";

  public readonly bool Finite;
  public readonly Expression TermLeft;

  public List<Boogie.Function> ProjectionFunctions;  // filled in during translation (and only for general map comprehensions where "TermLeft != null")

  public MapComprehension Clone(Cloner cloner) {
    return new MapComprehension(cloner, this);
  }

  public MapComprehension(Cloner cloner, MapComprehension original) : base(cloner, original) {
    TermLeft = cloner.CloneExpr(original.TermLeft);
    Finite = original.Finite;
  }

  public MapComprehension(IToken tok, RangeToken rangeToken, bool finite, List<BoundVar> bvars, Expression range, Expression/*?*/ termLeft, Expression termRight, Attributes attrs)
    : base(tok, rangeToken, bvars, range, termRight, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(cce.NonNullElements(bvars));
    Contract.Requires(1 <= bvars.Count);
    Contract.Requires(range != null);
    Contract.Requires(termRight != null);
    Contract.Requires(termLeft != null || bvars.Count == 1);

    Finite = finite;
    TermLeft = termLeft;
  }

  /// <summary>
  /// IsGeneralMapComprehension returns true for general map comprehensions.
  /// In other words, it returns false if either no TermLeft was given or if
  /// the given TermLeft is the sole bound variable.
  /// This property getter requires that the expression has been successfully
  /// resolved.
  /// </summary>
  public bool IsGeneralMapComprehension {
    get {
      Contract.Requires(WasResolved());
      if (TermLeft == null) {
        return false;
      } else if (BoundVars.Count != 1) {
        return true;
      }
      var lhs = StripParens(TermLeft).Resolved;
      if (lhs is IdentifierExpr ide && ide.Var == BoundVars[0]) {
        // TermLeft is the sole bound variable, so this is the same as
        // if TermLeft wasn't given at all
        return false;
      }
      return true;
    }
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      foreach (var e in Attributes.SubExpressions(Attributes)) {
        yield return e;
      }
      if (Range != null) { yield return Range; }
      if (TermLeft != null) { yield return TermLeft; }
      yield return Term;
    }
  }
}

public class LambdaExpr : ComprehensionExpr, ICloneable<LambdaExpr>, ICanFormat {
  public override string WhatKind => "lambda";

  public Expression Body => Term;

  public readonly List<FrameExpression> Reads;

  public LambdaExpr(IToken tok, RangeToken rangeToken, List<BoundVar> bvars, Expression requires, List<FrameExpression> reads, Expression body)
    : base(tok, rangeToken, bvars, requires, body, null) {
    Contract.Requires(reads != null);
    Reads = reads;
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return Term;
      if (Range != null) {
        yield return Range;
      }
      foreach (var read in Reads) {
        yield return read.E;
      }
    }
  }

  public LambdaExpr(Cloner cloner, LambdaExpr original) : base(cloner, original) {
    Reads = original.Reads.ConvertAll(cloner.CloneFrameExpr);
  }

  public LambdaExpr Clone(Cloner cloner) {
    return new LambdaExpr(cloner, this);
  }

  public override bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    var itemIndent = indentBefore + formatter.SpaceTab;
    var commaIndent = indentBefore;
    var firstSpec = true;
    var specIndent = indentBefore + formatter.SpaceTab;
    foreach (var token in OwnedTokens) {
      switch (token.val) {
        case "(": {
            if (TokenNewIndentCollector.IsFollowedByNewline(token)) {
              formatter.SetIndentations(token, indentBefore, indentBefore, itemIndent);
            } else {
              formatter.SetAlign(indentBefore, token, out itemIndent, out commaIndent);
            }

            break;
          }
        case ")": {
            formatter.SetIndentations(token, itemIndent, indentBefore, indentBefore);
            break;
          }
        case ",": {
            formatter.SetIndentations(token, itemIndent, commaIndent, itemIndent);
            break;
          }
        case "requires":
        case "reads": {
            if (firstSpec) {
              specIndent = formatter.GetNewTokenVisualIndent(token, indentBefore);
              firstSpec = false;
            }
            formatter.SetIndentations(token, specIndent, specIndent, specIndent + formatter.SpaceTab);
            break;
          }
        case "=>": {
            formatter.SetIndentations(token, itemIndent, indentBefore, indentBefore + formatter.SpaceTab);
            break;
          }
      }
    }

    foreach (var bv in BoundVars) {
      if (bv.SyntacticType != null) {
        formatter.SetTypeIndentation(bv.SyntacticType);
      }
    }

    return true;
  }
}

public class WildcardExpr : Expression {  // a WildcardExpr can occur only in reads clauses and a loop's decreases clauses (with different meanings)
  public WildcardExpr(IToken tok)
    : base(tok) {
    Contract.Requires(tok != null);
  }
}

/// <summary>
/// A StmtExpr has the form S;E where S is a statement (from a restricted set) and E is an expression.
/// The expression S;E evaluates to whatever E evaluates to, but its well-formedness comes down to
/// executing S (which itself must be well-formed) and then checking the well-formedness of E.
/// </summary>
public class StmtExpr : Expression, ICanFormat {
  public readonly Statement S;
  public readonly Expression E;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(S != null);
    Contract.Invariant(E != null);
  }

  public StmtExpr(IToken tok, Statement stmt, Expression expr)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(stmt != null);
    Contract.Requires(expr != null);
    S = stmt;
    E = expr;
  }
  public override IEnumerable<Expression> SubExpressions {
    get {
      // Note:  A StmtExpr is unusual in that it contains a statement.  For now, callers
      // of SubExpressions need to be aware of this and handle it specially.
      yield return E;
    }
  }

  public override IEnumerable<Expression> TerminalExpressions {
    get {
      foreach (var e in E.TerminalExpressions) {
        yield return e;
      }
    }
  }

  /// <summary>
  /// Returns a conclusion that S gives rise to, that is, something that is known after
  /// S is executed.
  /// This method should be called only after successful resolution of the expression.
  /// </summary>
  public Expression GetSConclusion() {
    // this is one place where we actually investigate what kind of statement .S is
    if (S is PredicateStmt) {
      var s = (PredicateStmt)S;
      return s.Expr;
    } else if (S is CalcStmt) {
      var s = (CalcStmt)S;
      return s.Result;
    } else if (S is RevealStmt) {
      return new LiteralExpr(tok, true);  // one could use the definition axiom or the referenced labeled assertions, but "true" is conservative and much simpler :)
    } else if (S is UpdateStmt) {
      return new LiteralExpr(tok, true);  // one could use the postcondition of the method, suitably instantiated, but "true" is conservative and much simpler :)
    } else {
      Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    formatter.Visit(S, indentBefore);
    formatter.SetIndentations(S.EndToken, below: indentBefore);
    formatter.Visit(E, indentBefore);
    return false;
  }
}

public class ITEExpr : Expression, ICanFormat {
  public readonly bool IsBindingGuard;
  public readonly Expression Test;
  public readonly Expression Thn;
  public readonly Expression Els;

  public enum ITECompilation {
    CompileBothBranches,
    CompileJustThenBranch,
    CompileJustElseBranch
  };
  public ITECompilation HowToCompile = ITECompilation.CompileBothBranches; // updated by CheckIsCompilable during resolution

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Test != null);
    Contract.Invariant(Thn != null);
    Contract.Invariant(Els != null);
  }

  public ITEExpr(IToken tok, bool isBindingGuard, Expression test, Expression thn, Expression els)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(test != null);
    Contract.Requires(thn != null);
    Contract.Requires(els != null);
    this.IsBindingGuard = isBindingGuard;
    this.Test = test;
    this.Thn = thn;
    this.Els = els;
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return Test;
      yield return Thn;
      yield return Els;
    }
  }

  public override IEnumerable<Expression> TerminalExpressions {
    get {
      foreach (var e in Thn.TerminalExpressions) {
        yield return e;
      }
      foreach (var e in Els.TerminalExpressions) {
        yield return e;
      }
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    var lineThen = 0;
    var colThen = 0;
    IToken thenToken = null;
    foreach (var token in OwnedTokens) {
      switch (token.val) {
        case "if": {
            if (TokenNewIndentCollector.IsFollowedByNewline(token)) {
              formatter.SetOpeningIndentedRegion(token, indentBefore);
            } else {
              formatter.SetAlignOpen(token, indentBefore);
            }
            formatter.Visit(Test, indentBefore);
            break;
          }
        case "then": {
            lineThen = token.line;
            colThen = token.col;
            thenToken = token;
            if (TokenNewIndentCollector.IsFollowedByNewline(token)) {
              formatter.SetOpeningIndentedRegion(token, indentBefore);
            } else {
              var rightIndent = formatter.GetRightAlignIndentAfter(token, indentBefore);
              formatter.SetIndentations(token, indentBefore, indentBefore, rightIndent);
            }
            formatter.Visit(Thn, indentBefore + formatter.SpaceTab);            // Override the last indentation so that comments are on the same column as "else"
            formatter.SetIndentations(token.Prev, below: indentBefore);

            break;
          }
        case "else": {
            if (token.col == colThen) {
              // We keep the alignment.
              var newElseIndent = formatter.GetNewTokenVisualIndent(thenToken, indentBefore);
              formatter.SetDelimiterIndentedRegions(token, newElseIndent);
            } else if (token.Next.val == "if" || token.line == lineThen) { // Don't indent the subexpression
              formatter.SetIndentations(token, above: indentBefore, inline: indentBefore, below: indentBefore);
            } else if (TokenNewIndentCollector.IsFollowedByNewline(token)) {
              formatter.SetOpeningIndentedRegion(token, indentBefore);
            } else {
              formatter.SetAlign(indentBefore, token, out _, out _);
            }

            formatter.Visit(Els, indentBefore + formatter.SpaceTab);
            // Override the last indentation so that comments are on the same column as "else"
            formatter.SetIndentations(token.Prev, below: indentBefore);
            break;
          }
      }
    }

    return false;
  }
}


/// <summary>
/// A CasePattern is either a BoundVar or a datatype constructor with optional arguments.
/// Lexically, the CasePattern starts with an identifier.  If it continues with an open paren (as
/// indicated by Arguments being non-null), then the CasePattern is a datatype constructor.  If
/// it continues with a colon (which is indicated by Var.Type not being a proxy type), then it is
/// a BoundVar.  But if it ends with just the identifier, then resolution is required to figure out
/// which it is; in this case, Var is non-null, because this is the only place where Var.IsGhost
/// is recorded by the parser.
/// </summary>
public class CasePattern<VT> : TokenNode
  where VT : class, IVariable {
  public readonly string Id;
  // After successful resolution, exactly one of the following two fields is non-null.

  [FilledInDuringResolution]
  public DatatypeCtor Ctor;  // finalized by resolution (null if the pattern is a bound variable)
  public VT Var;  // finalized by resolution (null if the pattern is a constructor)  Invariant:  Var != null ==> Arguments == null
  public List<CasePattern<VT>> Arguments;

  [FilledInDuringResolution] public Expression Expr;  // an r-value version of the CasePattern;

  public void MakeAConstructor() {
    this.Arguments = new List<CasePattern<VT>>();
  }

  public CasePattern(Cloner cloner, CasePattern<VT> original) {
    tok = cloner.Tok(original.tok);
    Id = original.Id;
    if (original.Var != null) {
      Var = cloner.CloneIVariable(original.Var, false);
    }

    if (cloner.CloneResolvedFields) {
      Expr = cloner.CloneExpr(original.Expr);
      Ctor = original.Ctor;
    }

    if (original.Arguments != null) {
      Arguments = original.Arguments.Select(cloner.CloneCasePattern).ToList();
    }
  }

  public CasePattern(IToken tok, string id, [Captured] List<CasePattern<VT>> arguments) {
    Contract.Requires(tok != null);
    Contract.Requires(id != null);
    this.tok = tok;
    Id = id;
    Arguments = arguments;
  }

  public CasePattern(IToken tok, VT bv) {
    Contract.Requires(tok != null);
    Contract.Requires(bv != null);
    this.tok = tok;
    Id = bv.Name;
    Var = bv;
  }

  /// <summary>
  /// Sets the Expr field.  Assumes the CasePattern and its arguments to have been successfully resolved, except for assigning
  /// to Expr.
  /// </summary>
  public void AssembleExpr(List<Type> dtvTypeArgs) {
    Contract.Requires(Var != null || dtvTypeArgs != null);
    if (Var != null) {
      Contract.Assert(this.Id == this.Var.Name);
      this.Expr = new IdentifierExpr(this.tok, this.Var);
    } else {
      var dtValue = new DatatypeValue(this.tok, this.Ctor.EnclosingDatatype.Name, this.Id,
        this.Arguments == null ? new List<Expression>() : this.Arguments.ConvertAll(arg => arg.Expr));
      dtValue.Ctor = this.Ctor;  // resolve here
      dtValue.InferredTypeArgs.AddRange(dtvTypeArgs);  // resolve here
      dtValue.Type = new UserDefinedType(this.tok, this.Ctor.EnclosingDatatype.Name, this.Ctor.EnclosingDatatype, dtvTypeArgs);
      this.Expr = dtValue;
    }
  }

  public IEnumerable<VT> Vars {
    get {
      if (Var != null) {
        yield return Var;
      } else {
        if (Arguments != null) {
          foreach (var arg in Arguments) {
            foreach (var bv in arg.Vars) {
              yield return bv;
            }
          }
        }
      }
    }
  }

  public override IEnumerable<Node> Children => Arguments ?? Enumerable.Empty<Node>();
  public override IEnumerable<Node> PreResolveChildren => Children;
}

public class BoxingCastExpr : Expression {  // a BoxingCastExpr is used only as a temporary placeholding during translation
  public readonly Expression E;
  public readonly Type FromType;
  public readonly Type ToType;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(E != null);
    Contract.Invariant(FromType != null);
    Contract.Invariant(ToType != null);
  }

  public BoxingCastExpr(Expression e, Type fromType, Type toType)
    : base(e.tok) {
    Contract.Requires(e != null);
    Contract.Requires(fromType != null);
    Contract.Requires(toType != null);

    E = e;
    FromType = fromType;
    ToType = toType;
  }

  public override IEnumerable<Expression> SubExpressions {
    get { yield return E; }
  }
}

public class UnboxingCastExpr : Expression {  // an UnboxingCastExpr is used only as a temporary placeholding during translation
  public readonly Expression E;
  public readonly Type FromType;
  public readonly Type ToType;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(E != null);
    Contract.Invariant(FromType != null);
    Contract.Invariant(ToType != null);
  }

  public UnboxingCastExpr(Expression e, Type fromType, Type toType)
    : base(e.tok) {
    Contract.Requires(e != null);
    Contract.Requires(fromType != null);
    Contract.Requires(toType != null);

    E = e;
    FromType = fromType;
    ToType = toType;
  }

  public override IEnumerable<Expression> SubExpressions {
    get { yield return E; }
  }
}

public class AttributedExpression : TokenNode, IAttributeBearingDeclaration {
  public readonly Expression E;
  public readonly AssertLabel/*?*/ Label;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(E != null);
  }

  private Attributes attributes;
  public Attributes Attributes {
    get {
      return attributes;
    }
    set {
      attributes = value;
    }
  }

  public override RangeToken RangeToken => E.RangeToken;

  public bool HasAttributes() {
    return Attributes != null;
  }

  public AttributedExpression(Expression e)
    : this(e, null) {
    Contract.Requires(e != null);
  }

  public AttributedExpression(Expression e, Attributes attrs) : this(e, null, attrs) {
  }

  public AttributedExpression(Expression e, AssertLabel/*?*/ label, Attributes attrs) {
    Contract.Requires(e != null);
    E = e;
    Label = label;
    Attributes = attrs;
    this.tok = e.Tok;
  }

  public void AddCustomizedErrorMessage(IToken tok, string s) {
    var args = new List<Expression>() { new StringLiteralExpr(tok, s, true) };
    IToken openBrace = tok;
    IToken closeBrace = new Token(tok.line, tok.col + 7 + s.Length + 1); // where 7 = length(":error ")
    this.Attributes = new UserSuppliedAttributes(tok, openBrace, closeBrace, args, this.Attributes);
  }

  public override IEnumerable<Node> Children =>
    (Attributes != null ? new List<Node>() { Attributes } : Enumerable.Empty<Node>()).Concat(
    new List<Node>() { E });

  public override IEnumerable<Node> PreResolveChildren => Children;
}

public class FrameExpression : TokenNode, IHasUsages {
  public readonly Expression OriginalExpression; // may be a WildcardExpr
  [FilledInDuringResolution] public Expression DesugaredExpression; // may be null for modifies clauses, even after resolution

  /// <summary>
  /// .E starts off as OriginalExpression; destructively updated to its desugared version during resolution
  /// </summary>
  public Expression E => DesugaredExpression ?? OriginalExpression;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(E != null);
    Contract.Invariant(!(E is WildcardExpr) || (FieldName == null && Field == null));
  }

  public readonly string FieldName;
  [FilledInDuringResolution] public Field Field;  // null if FieldName is

  /// <summary>
  /// If a "fieldName" is given, then "tok" denotes its source location.  Otherwise, "tok"
  /// denotes the source location of "e".
  /// </summary>
  public FrameExpression(IToken tok, Expression e, string fieldName) {
    Contract.Requires(tok != null);
    Contract.Requires(e != null);
    Contract.Requires(!(e is WildcardExpr) || fieldName == null);
    this.tok = tok;
    OriginalExpression = e;
    FieldName = fieldName;
  }

  public FrameExpression(Cloner cloner, FrameExpression original) {
    this.tok = cloner.Tok(original.tok);
    OriginalExpression = cloner.CloneExpr(original.OriginalExpression);
    FieldName = original.FieldName;

    if (cloner.CloneResolvedFields) {
      Field = original.Field;
      if (original.DesugaredExpression != null) {
        DesugaredExpression = cloner.CloneExpr(original.DesugaredExpression);
      }
    }
  }

  public IToken NameToken => tok;
  public override IEnumerable<Node> Children => new[] { E };
  public override IEnumerable<Node> PreResolveChildren => Children;
  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations() {
    return new[] { Field }.Where(x => x != null);
  }
}

/// <summary>
/// This class represents a piece of concrete syntax in the parse tree.  During resolution,
/// it gets "replaced" by the expression in "ResolvedExpression".
/// </summary>
public abstract class ConcreteSyntaxExpression : Expression {
  protected ConcreteSyntaxExpression(Cloner cloner, ConcreteSyntaxExpression original) : base(cloner, original) {
    if (cloner.CloneResolvedFields && original.ResolvedExpression != null) {
      ResolvedExpression = cloner.CloneExpr(original.ResolvedExpression);
    }
  }

  [FilledInDuringResolution]
  private Expression resolvedExpression;

  public Expression ResolvedExpression {
    get => resolvedExpression;
    set {
      resolvedExpression = value;
      if (rangeToken != null && resolvedExpression != null) {
        resolvedExpression.RangeToken = rangeToken;
      }
    }
  }  // after resolution, manipulation of "this" should proceed as with manipulating "this.ResolvedExpression"

  public ConcreteSyntaxExpression(IToken tok)
    : base(tok) {
  }
  public override IEnumerable<Node> Children => ResolvedExpression == null ? Array.Empty<Node>() : new[] { ResolvedExpression };
  public override IEnumerable<Expression> SubExpressions {
    get {
      if (ResolvedExpression != null) {
        yield return ResolvedExpression;
      }
    }
  }

  public override IEnumerable<Expression> TerminalExpressions {
    get {
      foreach (var e in ResolvedExpression.TerminalExpressions) {
        yield return e;
      }
    }
  }

  public virtual IEnumerable<Expression> PreResolveSubExpressions => Enumerable.Empty<Expression>();
  public override IEnumerable<Node> PreResolveChildren => PreResolveSubExpressions;

  public override IEnumerable<Type> ComponentTypes => ResolvedExpression.ComponentTypes;
}

public class ParensExpression : ConcreteSyntaxExpression, ICanFormat {
  public readonly Expression E;
  public ParensExpression(IToken tok, Expression e)
    : base(tok) {
    E = e;
  }

  protected ParensExpression(Cloner cloner, ParensExpression original) : base(cloner, original) {
    E = cloner.CloneExpr(original.E);
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      if (ResolvedExpression == null) {
        yield return E;
      } else {
        yield return ResolvedExpression;
      }
    }
  }

  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      yield return E;
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentParensExpression(indentBefore, OwnedTokens);
  }
}

public class DatatypeUpdateExpr : ConcreteSyntaxExpression, IHasUsages, ICloneable<DatatypeUpdateExpr> {
  public readonly Expression Root;
  public readonly List<Tuple<IToken, string, Expression>> Updates;
  [FilledInDuringResolution] public List<MemberDecl> Members;
  [FilledInDuringResolution] public List<DatatypeCtor> LegalSourceConstructors;
  [FilledInDuringResolution] public bool InCompiledContext;
  [FilledInDuringResolution] public Expression ResolvedCompiledExpression; // see comment for Resolver.ResolveDatatypeUpdate

  public DatatypeUpdateExpr Clone(Cloner cloner) {
    return new DatatypeUpdateExpr(cloner, this);
  }

  public DatatypeUpdateExpr(Cloner cloner, DatatypeUpdateExpr original) : base(cloner, original) {
    Root = cloner.CloneExpr(original.Root);
    Updates = original.Updates.Select(t => Tuple.Create(cloner.Tok(t.Item1), t.Item2, cloner.CloneExpr(t.Item3)))
      .ToList();

    if (cloner.CloneResolvedFields) {
      Members = original.Members;
      LegalSourceConstructors = original.LegalSourceConstructors;
      InCompiledContext = original.InCompiledContext;
      ResolvedCompiledExpression = cloner.CloneExpr(original.ResolvedCompiledExpression);
    }
  }

  public DatatypeUpdateExpr(IToken tok, Expression root, List<Tuple<IToken, string, Expression>> updates)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(root != null);
    Contract.Requires(updates != null);
    Contract.Requires(updates.Count != 0);
    Root = root;
    Updates = updates;
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      if (ResolvedExpression == null) {
        foreach (var preResolved in PreResolveSubExpressions) {

          yield return preResolved;
        }
      } else {
        foreach (var e in base.SubExpressions) {
          yield return e;
        }
      }
    }
  }

  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations() {
    return LegalSourceConstructors;
  }

  public IToken NameToken => tok;

  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      yield return Root;
      foreach (var update in Updates) {
        yield return update.Item3;
      }
    }
  }
}

/// <summary>
/// An AutoGeneratedExpression is simply a wrapper around an expression.  This expression tells the generation of hover text (in the Dafny IDE)
/// that the expression was no supplied directly in the program text and should therefore be ignored.  In other places, an AutoGeneratedExpression
/// is just a parenthesized expression, which means that it works just the like expression .E that it contains.
/// (Ironically, AutoGeneratedExpression, which is like the antithesis of concrete syntax, inherits from ConcreteSyntaxExpression, which perhaps
/// should rather have been called SemanticsNeutralExpressionWrapper.)
/// </summary>
// TODO replace this with AutoGeneratedToken.
public class AutoGeneratedExpression : ParensExpression, ICloneable<AutoGeneratedExpression> {
  public AutoGeneratedExpression(IToken tok, Expression e)
    : base(tok, e) {
    Contract.Requires(tok != null);
    Contract.Requires(e != null);
  }

  public AutoGeneratedExpression Clone(Cloner cloner) {
    return new AutoGeneratedExpression(cloner, this);
  }

  public AutoGeneratedExpression(Cloner cloner, AutoGeneratedExpression original) : base(cloner, original) {
  }

  /// <summary>
  /// This maker method takes a resolved expression "e" and wraps a resolved AutoGeneratedExpression
  /// around it.
  /// </summary>
  public static AutoGeneratedExpression Create(Expression e, IToken token = null) {
    Contract.Requires(e != null);
    var a = new AutoGeneratedExpression(token ?? e.tok, e);
    a.type = e.Type;
    a.ResolvedExpression = e;
    return a;
  }
}

/// <summary>
/// When an actual parameter is omitted for a formal with a default value, the positional resolved
/// version of the actual parameter will have a DefaultValueExpression value. This has three
/// advantages:
/// * It allows the entire module to be resolved before any substitutions take place.
/// * It gives a good place to check for default-value expressions that would give rise to an
///   infinite expansion.
/// * It preserves the pre-substitution form, which gives compilers a chance to avoid re-evaluation
///   of actual parameters used in other default-valued expressions.
///
/// Note. Since DefaultValueExpression is a wrapper around another expression and can in several
/// places be expanded according to its ResolvedExpression, it is convenient to make DefaultValueExpression
/// inherit from ConcreteSyntaxExpression. However, there are some places in the code where
/// one then needs to pay attention to DefaultValueExpression's. Such places would be more
/// conspicuous if DefaultValueExpression were not an Expression at all. At the time of this
/// writing, a change to a separate type has shown to be more hassle than the need for special
/// attention to DefaultValueExpression's in some places.
/// </summary>
public class DefaultValueExpression : ConcreteSyntaxExpression, ICloneable<DefaultValueExpression> {
  public readonly Formal Formal;
  public readonly Expression Receiver;
  public readonly Dictionary<IVariable, Expression> SubstMap;
  public readonly Dictionary<TypeParameter, Type> TypeMap;

  public DefaultValueExpression(IToken tok, Formal formal,
    Expression/*?*/ receiver, Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, Type> typeMap)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(formal != null);
    Contract.Requires(formal.DefaultValue != null);
    Contract.Requires(substMap != null);
    Contract.Requires(typeMap != null);
    Formal = formal;
    Receiver = receiver;
    SubstMap = substMap;
    TypeMap = typeMap;
    Type = formal.Type.Subst(typeMap);
    RangeToken = new RangeToken(tok, tok);
  }

  public DefaultValueExpression(Cloner cloner, DefaultValueExpression original) : base(cloner, original) {
    if (!cloner.CloneResolvedFields) {
      throw new InvalidOperationException("DefaultValueExpression is created during resolution");
    }
    Formal = cloner.CloneFormal(original.Formal, true);
    Receiver = cloner.CloneExpr(original.Receiver);
    SubstMap = original.SubstMap;
    TypeMap = original.TypeMap;
  }

  public DefaultValueExpression Clone(Cloner cloner) {
    return new DefaultValueExpression(cloner, this);
  }
}

/// <summary>
/// A NegationExpression e represents the value -e and is syntactic shorthand
/// for 0-e (for integers) or 0.0-e (for reals).
/// </summary>
public class NegationExpression : ConcreteSyntaxExpression, ICloneable<NegationExpression> {
  public readonly Expression E;

  public NegationExpression Clone(Cloner cloner) {
    return new NegationExpression(cloner, this);
  }

  public NegationExpression(Cloner cloner, NegationExpression original) : base(cloner, original) {
    E = cloner.CloneExpr(original.E);
  }

  public NegationExpression(IToken tok, Expression e)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(e != null);
    E = e;
  }
  public override IEnumerable<Expression> SubExpressions {
    get {
      if (ResolvedExpression == null) {
        // the expression hasn't yet been turned into a resolved expression, so use .E as the subexpression
        yield return E;
      } else {
        foreach (var ee in base.SubExpressions) {
          yield return ee;
        }
      }
    }
  }

  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      yield return E;
    }
  }
}

public class ChainingExpression : ConcreteSyntaxExpression, ICloneable<ChainingExpression>, ICanFormat {
  public readonly List<Expression> Operands;
  public readonly List<BinaryExpr.Opcode> Operators;
  public readonly List<IToken> OperatorLocs;
  public readonly List<Expression/*?*/> PrefixLimits;
  public readonly Expression E;

  public ChainingExpression Clone(Cloner cloner) {
    return new ChainingExpression(cloner, this);
  }

  public ChainingExpression(Cloner cloner, ChainingExpression original) : base(cloner, original) {
    Operands = original.Operands.Select(cloner.CloneExpr).ToList();
    Operators = original.Operators;
    OperatorLocs = original.OperatorLocs.Select(cloner.Tok).ToList();
    PrefixLimits = original.PrefixLimits.Select(cloner.CloneExpr).ToList();
    E = ComputeDesugaring(Operands, Operators, OperatorLocs, PrefixLimits);
  }

  public ChainingExpression(IToken tok, List<Expression> operands, List<BinaryExpr.Opcode> operators, List<IToken> operatorLocs, List<Expression/*?*/> prefixLimits)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(operands != null);
    Contract.Requires(operators != null);
    Contract.Requires(operatorLocs != null);
    Contract.Requires(prefixLimits != null);
    Contract.Requires(1 <= operators.Count);
    Contract.Requires(operands.Count == operators.Count + 1);
    Contract.Requires(operatorLocs.Count == operators.Count);
    Contract.Requires(prefixLimits.Count == operators.Count);
    // Additional preconditions apply, see Contract.Assume's below

    Operands = operands;
    Operators = operators;
    OperatorLocs = operatorLocs;
    PrefixLimits = prefixLimits;
    E = ComputeDesugaring(operands, operators, operatorLocs, prefixLimits);
  }

  private static Expression ComputeDesugaring(List<Expression> operands, List<BinaryExpr.Opcode> operators, List<IToken> operatorLocs, List<Expression> prefixLimits) {
    Expression desugaring;
    // Compute the desugaring
    if (operators[0] == BinaryExpr.Opcode.Disjoint) {
      Expression acc = operands[0]; // invariant:  "acc" is the union of all operands[j] where j <= i
      desugaring = new BinaryExpr(operatorLocs[0], operators[0], operands[0], operands[1]);
      for (int i = 0; i < operators.Count; i++) {
        Contract.Assume(operators[i] == BinaryExpr.Opcode.Disjoint);
        var opTok = operatorLocs[i];
        var e = new BinaryExpr(opTok, BinaryExpr.Opcode.Disjoint, acc, operands[i + 1]);
        desugaring = new BinaryExpr(opTok, BinaryExpr.Opcode.And, desugaring, e);
        acc = new BinaryExpr(opTok, BinaryExpr.Opcode.Add, acc, operands[i + 1]);
      }
    } else {
      desugaring = null;
      for (int i = 0; i < operators.Count; i++) {
        var opTok = operatorLocs[i];
        var op = operators[i];
        Contract.Assume(op != BinaryExpr.Opcode.Disjoint);
        var k = prefixLimits[i];
        Contract.Assume(k == null || op == BinaryExpr.Opcode.Eq || op == BinaryExpr.Opcode.Neq);
        var e0 = operands[i];
        var e1 = operands[i + 1];
        Expression e;
        if (k == null) {
          e = new BinaryExpr(opTok, op, e0, e1);
        } else {
          e = new TernaryExpr(opTok,
            op == BinaryExpr.Opcode.Eq ? TernaryExpr.Opcode.PrefixEqOp : TernaryExpr.Opcode.PrefixNeqOp, k, e0,
            e1);
        }

        desugaring = desugaring == null ? e : new BinaryExpr(opTok, BinaryExpr.Opcode.And, desugaring, e);
      }
    }

    return desugaring;
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      if (!WasResolved()) {
        foreach (var sub in PreResolveSubExpressions) {
          yield return sub;
        }
      } else {
        yield return Resolved;
      }
    }
  }
  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      foreach (var sub in Operands) {
        yield return sub;
      }
      foreach (var sub in PrefixLimits) {
        if (sub != null) {
          yield return sub;
        }
      }
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    // Chaining expressions try to align their values if possible
    var itemIndent = formatter.GetNewTokenVisualIndent(
      Operands[0].StartToken, indentBefore);

    foreach (var token in OwnedTokens) {
      switch (token.val) {
        case "[":
          break;
        case "#":
          break;
        case "]":
          break;
        default:
          formatter.SetIndentations(token, itemIndent, Math.Max(itemIndent - token.val.Length - 1, 0), itemIndent);
          break;
      }
    }

    return true;
  }
}

/// <summary>
/// The parsing and resolution/type checking of expressions of the forms
///   0. ident &lt; Types &gt;
///   1. Expr . ident &lt; Types &gt;
///   2. Expr ( Exprs )
///   3. Expr [ Exprs ]
///   4. Expr [ Expr .. Expr ]
/// is done as follows.  These forms are parsed into the following AST classes:
///   0. NameSegment
///   1. ExprDotName
///   2. ApplySuffix
///   3. SeqSelectExpr or MultiSelectExpr
///   4. SeqSelectExpr
///
/// The first three of these inherit from ConcreteSyntaxExpression.  The resolver will resolve
/// these into:
///   0. IdentifierExpr or MemberSelectExpr (with .Lhs set to ImplicitThisExpr or StaticReceiverExpr)
///   1. IdentifierExpr or MemberSelectExpr
///   2. FuncionCallExpr or ApplyExpr
///
/// The IdentifierExpr's that forms 0 and 1 can turn into sometimes denote the name of a module or
/// type.  The .Type field of the corresponding resolved expressions are then the special Type subclasses
/// ResolutionType_Module and ResolutionType_Type, respectively.  These will not be seen by the
/// verifier or compiler, since, in a well-formed program, the verifier and compiler will use the
/// .ResolvedExpr field of whatever form-1 expression contains these.
///
/// Notes:
///   * IdentifierExpr and FunctionCallExpr are resolved-only expressions (that is, they don't contain
///     all the syntactic components that were used to parse them).
///   * Rather than the current SeqSelectExpr/MultiSelectExpr split of forms 3 and 4, it would
///     seem more natural to refactor these into 3: IndexSuffixExpr and 4: RangeSuffixExpr.
/// </summary>
public abstract class SuffixExpr : ConcreteSyntaxExpression {
  public readonly Expression Lhs;

  protected SuffixExpr(Cloner cloner, SuffixExpr original) : base(cloner, original) {
    Lhs = cloner.CloneExpr(original.Lhs);
  }

  public SuffixExpr(IToken tok, Expression lhs)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(lhs != null);
    Lhs = lhs;
  }

  public override IEnumerable<Node> Children => ResolvedExpression == null ? new[] { Lhs } : base.Children;
  public override IEnumerable<Node> PreResolveChildren => PreResolveSubExpressions;

  public override IEnumerable<Expression> SubExpressions {
    get {
      if (!WasResolved()) {
        foreach (var sub in PreResolveSubExpressions) {
          yield return sub;
        }
      } else if (Resolved != null) {
        yield return Resolved;
      }
    }
  }

  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      yield return Lhs;
    }
  }
}

public class NameSegment : ConcreteSyntaxExpression, ICloneable<NameSegment> {
  public readonly string Name;
  public readonly List<Type> OptTypeArguments;
  public NameSegment(IToken tok, string name, List<Type> optTypeArguments)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Contract.Requires(optTypeArguments == null || optTypeArguments.Count > 0);
    Name = name;
    OptTypeArguments = optTypeArguments;
  }

  public NameSegment(Cloner cloner, NameSegment original) : base(cloner, original) {
    Name = original.Name;
    OptTypeArguments = original.OptTypeArguments?.ConvertAll(cloner.CloneType);
  }

  public NameSegment Clone(Cloner cloner) {
    return new NameSegment(cloner, this);
  }

  public override IEnumerable<Node> PreResolveChildren => OptTypeArguments ?? new List<Type>();
}

/// <summary>
/// An ExprDotName desugars into either an IdentifierExpr (if the Lhs is a static name) or a MemberSelectExpr (if the Lhs is a computed expression).
/// </summary>
public class ExprDotName : SuffixExpr, ICloneable<ExprDotName> {
  public readonly string SuffixName;
  public readonly List<Type> OptTypeArguments;

  /// <summary>
  /// Because the resolved expression only points to the final resolved declaration,
  /// but not the declaration of the Lhs, we must also include the Lhs.
  /// </summary>
  public override IEnumerable<Node> Children => new[] { Lhs, ResolvedExpression };

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(SuffixName != null);
  }

  public ExprDotName Clone(Cloner cloner) {
    return new ExprDotName(cloner, this);
  }

  public ExprDotName(Cloner cloner, ExprDotName original) : base(cloner, original) {
    SuffixName = original.SuffixName;
    OptTypeArguments = original.OptTypeArguments?.ConvertAll(cloner.CloneType);
  }

  public ExprDotName(IToken tok, Expression obj, string suffixName, List<Type> optTypeArguments)
    : base(tok, obj) {
    Contract.Requires(tok != null);
    Contract.Requires(obj != null);
    Contract.Requires(suffixName != null);
    this.SuffixName = suffixName;
    OptTypeArguments = optTypeArguments;
  }
}

/// <summary>
/// An ApplySuffix desugars into either an ApplyExpr or a FunctionCallExpr
/// </summary>
public class ApplySuffix : SuffixExpr, ICloneable<ApplySuffix>, ICanFormat {
  public readonly IToken/*?*/ AtTok;
  public readonly IToken CloseParen;
  public readonly ActualBindings Bindings;
  public List<Expression> Args => Bindings.Arguments;

  public override IEnumerable<Node> Children => ResolvedExpression == null
    ? base.Children.Concat(Bindings == null ? new List<Node>() : Args ?? Enumerable.Empty<Node>()) : new[] { ResolvedExpression };
  public override IEnumerable<Node> PreResolveChildren => new List<Node> { Lhs, Bindings };

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Args != null);
  }

  public ApplySuffix Clone(Cloner cloner) {
    return new ApplySuffix(cloner, this);
  }

  public ApplySuffix(Cloner cloner, ApplySuffix original) :
    base(cloner, original) {
    AtTok = original.AtTok == null ? null : cloner.Tok(original.AtTok);
    CloseParen = cloner.Tok(original.CloseParen);
    FormatTokens = original.FormatTokens;
    Bindings = new ActualBindings(cloner, original.Bindings);
  }

  public ApplySuffix(IToken tok, IToken/*?*/ atLabel, Expression lhs, List<ActualBinding> args, IToken closeParen)
    : base(tok, lhs) {
    Contract.Requires(tok != null);
    Contract.Requires(lhs != null);
    Contract.Requires(cce.NonNullElements(args));
    AtTok = atLabel;
    CloseParen = closeParen;
    Bindings = new ActualBindings(args);
    if (closeParen != null) {
      FormatTokens = new[] { closeParen };
    }
  }

  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      yield return Lhs;
      if (Bindings.ArgumentBindings != null) {
        foreach (var binding in Bindings.ArgumentBindings) {
          yield return binding.Actual;
        }
      }
    }
  }

  /// <summary>
  /// Create an ApplySuffix expression using the most basic pieces: a target name and a list of expressions.
  /// </summary>
  /// <param name="tok">The location to associate with the new ApplySuffix expression.</param>
  /// <param name="name">The name of the target function or method.</param>
  /// <param name="args">The arguments to apply the function or method to.</param>
  /// <returns></returns>
  public static Expression MakeRawApplySuffix(IToken tok, string name, List<Expression> args) {
    var nameExpr = new NameSegment(tok, name, null);
    var argBindings = args.ConvertAll(arg => new ActualBinding(null, arg));
    return new ApplySuffix(tok, null, nameExpr, argBindings, tok);
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    var reindent = formatter.ReduceBlockiness ? indentBefore
      : formatter.GetNewTokenVisualIndent(StartToken, indentBefore);
    return formatter.SetIndentParensExpression(reindent, OwnedTokens);
  }
}
