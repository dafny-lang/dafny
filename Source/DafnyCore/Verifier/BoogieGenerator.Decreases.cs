using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Reflection;
using System.Security.Cryptography;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading;
using Microsoft.Boogie;
using static Microsoft.Dafny.Util;
using Core;
using DafnyCore.Verifier;
using Microsoft.BaseTypes;
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.Triggers;
using Action = System.Action;
using PODesc = Microsoft.Dafny.ProofObligationDescription;
using static Microsoft.Dafny.GenericErrors;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {


  /// <summary>
  /// Emit to "builder" a check that calleeDecreases is less than contextDecreases.  More precisely,
  /// the check is:
  ///     allowance || (calleeDecreases LESS contextDecreases).
  /// </summary>
  void CheckCallTermination(IOrigin tok, List<Expression> contextDecreases, List<Expression> calleeDecreases,
                            Expression allowance,
                            Expression receiverReplacement, Dictionary<IVariable, Expression> substMap,
                            Dictionary<IVariable, Expression> directSubstMap,
                            Dictionary<TypeParameter, Type> typeMap,
                            ExpressionTranslator etranCurrent, bool oldCaller, BoogieStmtListBuilder builder, bool inferredDecreases, string hint) {
    Contract.Requires(tok != null);
    Contract.Requires(cce.NonNullElements(contextDecreases));
    Contract.Requires(cce.NonNullElements(calleeDecreases));
    Contract.Requires(cce.NonNullDictionaryAndValues(substMap));
    Contract.Requires(etranCurrent != null);
    Contract.Requires(builder != null);

    // The interpretation of the given decreases-clause expression tuples is as a lexicographic tuple, extended into
    // an infinite tuple by appending TOP elements.  The TOP element is strictly larger than any other value given
    // by a Dafny expression.  Each Dafny types has its own ordering, and these orderings are combined into a partial
    // order where elements from different Dafny types are incomparable.  Thus, as an optimization below, if two
    // components from different types are compared, the answer is taken to be false.

    if (Contract.Exists(calleeDecreases, e => e is WildcardExpr)) {
      // no check needed
      return;
    }

    int N = Math.Min(contextDecreases.Count, calleeDecreases.Count);
    var toks = new List<IOrigin>();
    var callee = new List<Expr>();
    var caller = new List<Expr>();
    var oldExpressions = new List<Expression>();
    var newExpressions = new List<Expression>();
    if (tok.IsInherited(currentModule) && contextDecreases.All(e => !e.Tok.IsInherited(currentModule))) {
      // the call site is inherited but all the context decreases expressions are new
      tok = new ForceCheckOrigin(tok);
    }
    for (int i = 0; i < N; i++) {
      Expression e0 = Substitute(calleeDecreases[i], receiverReplacement, substMap, typeMap);
      Expression e0direct = Substitute(calleeDecreases[i], receiverReplacement, directSubstMap, typeMap);
      Expression e1 = contextDecreases[i];
      if (oldCaller) {
        e1 = new OldExpr(e1.Tok, e1) {
          Type = e1.Type // To ensure that e1 stays resolved
        };
      }
      if (!CompatibleDecreasesTypes(e0.Type, e1.Type)) {
        N = i;
        break;
      }
      oldExpressions.Add(e1);
      newExpressions.Add(e0direct);
      toks.Add(new NestedOrigin(tok, e1.Tok));
      callee.Add(etranCurrent.TrExpr(e0));
      caller.Add(etranCurrent.TrExpr(e1));
    }
    bool endsWithWinningTopComparison = N == contextDecreases.Count && N < calleeDecreases.Count;
    Bpl.Expr decrExpr = DecreasesCheck(toks, null, newExpressions, oldExpressions, callee, caller, builder, "", endsWithWinningTopComparison, false);
    if (allowance != null) {
      decrExpr = BplOr(etranCurrent.TrExpr(allowance), decrExpr);
    }
    builder.Add(Assert(tok, decrExpr, new
      Terminates(inferredDecreases, null, allowance,
                        oldExpressions, newExpressions, endsWithWinningTopComparison, hint), builder.Context));
  }

  /// <summary>
  /// Returns the expression that says whether or not the decreases function has gone down (if !allowNoChange)
  /// or has gone down or stayed the same (if allowNoChange).
  /// ee0 represents the new values and ee1 represents old values.
  /// If builder is non-null, then the check '0 ATMOST decr' is generated to builder.
  /// Requires all types in types0 and types1 to be non-proxy non-synonym types (that is, callers should invoke NormalizeExpand)
  /// </summary>
  Bpl.Expr DecreasesCheck(List<IOrigin> toks, List<VarDeclStmt> prevGhostLocals,
                          List<Expression> dafny0, List<Expression> dafny1, List<Bpl.Expr> ee0, List<Bpl.Expr> ee1,
                          BoogieStmtListBuilder builder, string suffixMsg, bool allowNoChange, bool includeLowerBound) {
    Contract.Requires(cce.NonNullElements(toks));
    Contract.Requires(cce.NonNullElements(dafny0));
    Contract.Requires(cce.NonNullElements(dafny1));
    Contract.Requires(cce.NonNullElements(ee0));
    Contract.Requires(cce.NonNullElements(ee1));
    Contract.Requires(Predef != null);
    Contract.Requires(dafny0.Count == dafny1.Count && dafny0.Count == ee0.Count && ee0.Count == ee1.Count);
    Contract.Requires(builder == null || suffixMsg != null);
    Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

    int N = dafny0.Count;

    // compute eq and less for each component of the lexicographic tuple
    List<Bpl.Expr> Eq = new List<Bpl.Expr>(N);
    List<Bpl.Expr> Less = new List<Bpl.Expr>(N);
    List<Expression> EqDafny = new List<Expression>(N);
    List<Expression> LessDafny = new List<Expression>(N);
    for (int i = 0; i < N; i++) {
      Bpl.Expr less, atmost, eq;
      var ty0 = dafny0[i].Type.NormalizeExpandKeepConstraints();
      var ty1 = dafny1[i].Type.NormalizeExpandKeepConstraints();
      ComputeLessEq(toks[i], ty0, ty1, ee0[i], ee1[i], out less, out atmost, out eq, includeLowerBound);
      Eq.Add(eq);
      EqDafny.Add(Expression.CreateEq(dafny0[i], dafny1[i], dafny0[i].Type.NormalizeExpand()));
      Less.Add(allowNoChange ? atmost : less);
      LessDafny.Add(
        allowNoChange
          ? Expression.CreateAtMost(dafny0[i], dafny1[i])
          : Expression.CreateLess(dafny0[i], dafny1[i]));
    }
    if (builder != null) {
      // check: 0 <= ee1
      // more precisely, for component k of the lexicographic decreases function, check:
      //   ee0[0] < ee1[0] || ee0[1] < ee1[1] || ... || ee0[k-1] < ee1[k-1] || ee0[k] == ee1[k] || 0 <= ee1[k]
      for (int k = 0; k < N; k++) {
        // we only need to check lower bound for integers--sets, sequences, booleans, references, and datatypes all have natural lower bounds
        Bpl.Expr prefixIsLess = Bpl.Expr.False;
        for (int i = 0; i < k; i++) {
          prefixIsLess = BplOr(prefixIsLess, Less[i]);
        };

        Bpl.Expr zero = null;
        Expression dafnyZero = null;
        string zeroStr = null;
        if (dafny0[k].Type.NormalizeExpandKeepConstraints().IsNumericBased(Type.NumericPersuasion.Int)) {
          zero = Bpl.Expr.Literal(0);
          dafnyZero = Expression.CreateIntLiteral(dafny0[k].Tok, 0);
          zeroStr = "0";
        } else if (dafny0[k].Type.NormalizeExpandKeepConstraints().IsNumericBased(Type.NumericPersuasion.Real)) {
          zero = Bpl.Expr.Literal(BaseTypes.BigDec.ZERO);
          dafnyZero = Expression.CreateRealLiteral(dafny0[k].Tok, BigDec.ZERO);
          zeroStr = "0.0";
        }
        if (zero != null) {
          Bpl.Expr bounded = Bpl.Expr.Le(zero, ee1[k]);
          Expression boundedDafny = Expression.CreateAtMost(dafnyZero, dafny1[k]);
          for (int i = 0; i < k; i++) {
            bounded = BplOr(bounded, Less[i]);
            boundedDafny = Expression.CreateOr(boundedDafny, LessDafny[i]);
          }

          Expression dafnyBound = Expression.CreateOr(boundedDafny, EqDafny[k]);
          Bpl.Cmd cmd = Assert(toks[k], BplOr(bounded, Eq[k]),
            new DecreasesBoundedBelow(N, k, zeroStr, prevGhostLocals, dafnyBound, suffixMsg), builder.Context);
          builder.Add(cmd);
        }
      }
    }
    // check: ee0 < ee1 (or ee0 <= ee1, if allowNoChange)
    Bpl.Expr decrCheck = allowNoChange ? Bpl.Expr.True : Bpl.Expr.False;
    for (int i = N; 0 <= --i;) {
      Bpl.Expr less = Less[i];
      Bpl.Expr eq = Eq[i];
      if (allowNoChange) {
        // decrCheck = atmost && (eq ==> decrCheck)
        decrCheck = BplAnd(less, BplImp(eq, decrCheck));
      } else {
        // decrCheck = less || (eq && decrCheck)
        decrCheck = BplOr(less, BplAnd(eq, decrCheck));
      }
    }
    return decrCheck;
  }

  static bool CompatibleDecreasesTypes(Type t, Type u) {
    Contract.Requires(t != null);
    Contract.Requires(u != null);
    t = t.NormalizeToAncestorType();
    u = u.NormalizeToAncestorType();
    if (t is BoolType) {
      return u is BoolType;
    } else if (t is CharType) {
      return u is CharType;
    } else if (t is IntType) {
      // we can allow different kinds of int-based types
      return u is IntType;
    } else if (t is RealType) {
      // we can allow different kinds of real-based types
      return u is RealType;
    } else if (t is SetType) {
      return u is SetType;
    } else if (t is SeqType) {
      return u is SeqType || u.IsIndDatatype;
    } else if (t.IsDatatype) {
      return u.IsDatatype || (t.IsIndDatatype && u is SeqType);
    } else if (t.IsRefType) {
      return u.IsRefType;
    } else if (t is MultiSetType) {
      return u is MultiSetType;
    } else if (t is MapType) {
      return u is MapType && ((MapType)t).Finite == ((MapType)u).Finite;
    } else if (t is ArrowType) {
      return u is ArrowType;
    } else if (t is BitvectorType) {
      return u is BitvectorType;
    } else if (t is BigOrdinalType) {
      return u is BigOrdinalType;
    } else if (t.IsTypeParameter || t.IsAbstractType || t.IsInternalTypeSynonym) {
      return false;  // don't consider any type parameters to be the same (since we have no comparison function for them anyway)
    } else {
      return t.Equals(u);
    }
  }

  Nullable<BuiltinFunction> RankFunction(Type/*!*/ ty) {
    Contract.Requires(ty != null);
    if (ty is SeqType) {
      return BuiltinFunction.SeqRank;
    } else if (ty.IsIndDatatype) {
      return BuiltinFunction.DtRank;
    } else {
      return null;
    }
  }

  void ComputeLessEq(IOrigin tok, Type ty0, Type ty1, Bpl.Expr e0, Bpl.Expr e1, out Bpl.Expr less, out Bpl.Expr atmost, out Bpl.Expr eq, bool includeLowerBound) {
    Contract.Requires(tok != null);
    Contract.Requires(ty0 != null);
    Contract.Requires(ty1 != null);
    Contract.Requires(e0 != null);
    Contract.Requires(e1 != null);
    Contract.Requires(Predef != null);
    Contract.Ensures(Contract.ValueAtReturn(out less) != null);
    Contract.Ensures(Contract.ValueAtReturn(out atmost) != null);
    Contract.Ensures(Contract.ValueAtReturn(out eq) != null);

    ty0 = ty0.NormalizeToAncestorType();
    ty1 = ty1.NormalizeToAncestorType();
    var rk0 = RankFunction(ty0);
    var rk1 = RankFunction(ty1);
    if (rk0 != null && rk1 != null && rk0 != rk1) {
      eq = Bpl.Expr.False;
      Bpl.Expr b0 = FunctionCall(tok, rk0.Value, null, e0);
      Bpl.Expr b1 = FunctionCall(tok, rk1.Value, null, e1);
      less = Bpl.Expr.Lt(b0, b1);
      atmost = Bpl.Expr.Le(b0, b1);
    } else if (ty0 is BoolType) {
      eq = BplIff(e0, e1);
      less = BplAnd(Bpl.Expr.Not(e0), e1);
      atmost = BplImp(e0, e1);
    } else if (ty0 is CharType) {
      eq = Bpl.Expr.Eq(e0, e1);
      var operand0 = FunctionCall(e0.tok, BuiltinFunction.CharToInt, null, e0);
      var operand1 = FunctionCall(e0.tok, BuiltinFunction.CharToInt, null, e1);
      less = Bpl.Expr.Binary(tok, BinaryOperator.Opcode.Lt, operand0, operand1);
      atmost = Bpl.Expr.Binary(tok, BinaryOperator.Opcode.Le, operand0, operand1);
    } else if (ty0.IsNumericBased(Type.NumericPersuasion.Int) || ty0 is SeqType || ty0.IsDatatype) {
      Bpl.Expr b0, b1;
      if (ty0.IsNumericBased(Type.NumericPersuasion.Int)) {
        b0 = e0;
        b1 = e1;
      } else if (ty0 is SeqType) {
        b0 = FunctionCall(tok, BuiltinFunction.SeqRank, null, e0);
        b1 = FunctionCall(tok, BuiltinFunction.SeqRank, null, e1);
      } else if (ty0.IsDatatype) {
        b0 = FunctionCall(tok, BuiltinFunction.DtRank, null, e0);
        b1 = FunctionCall(tok, BuiltinFunction.DtRank, null, e1);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
      eq = Bpl.Expr.Eq(b0, b1);
      less = Bpl.Expr.Lt(b0, b1);
      atmost = Bpl.Expr.Le(b0, b1);
      if (ty0.IsNumericBased(Type.NumericPersuasion.Int) && includeLowerBound) {
        less = BplAnd(Bpl.Expr.Le(Bpl.Expr.Literal(0), b0), less);
        atmost = BplAnd(Bpl.Expr.Le(Bpl.Expr.Literal(0), b0), atmost);
      }

    } else if (ty0.IsNumericBased(Type.NumericPersuasion.Real)) {
      eq = Bpl.Expr.Eq(e0, e1);
      less = Bpl.Expr.Le(e0, Bpl.Expr.Sub(e1, Bpl.Expr.Literal(BaseTypes.BigDec.FromInt(1))));
      atmost = Bpl.Expr.Le(e0, e1);
      if (includeLowerBound) {
        less = BplAnd(Bpl.Expr.Le(Bpl.Expr.Literal(BaseTypes.BigDec.ZERO), e0), less);
        atmost = BplAnd(Bpl.Expr.Le(Bpl.Expr.Literal(BaseTypes.BigDec.ZERO), e0), atmost);
      }

    } else if (ty0 is IteratorDecl.EverIncreasingType) {
      eq = Bpl.Expr.Eq(e0, e1);
      less = Bpl.Expr.Gt(e0, e1);
      atmost = Bpl.Expr.Ge(e0, e1);

    } else if (ty0 is SetType { Finite: true } || ty0 is MapType { Finite: true }) {
      Bpl.Expr b0, b1;
      if (ty0 is SetType) {
        b0 = e0;
        b1 = e1;
      } else {
        // for maps, compare their domains as sets
        b0 = FunctionCall(tok, BuiltinFunction.MapDomain, Predef.MapType, e0);
        b1 = FunctionCall(tok, BuiltinFunction.MapDomain, Predef.MapType, e1);
      }
      eq = FunctionCall(tok, BuiltinFunction.SetEqual, null, b0, b1);
      less = ProperSubset(tok, b0, b1, true);
      atmost = FunctionCall(tok, BuiltinFunction.SetSubset, null, b0, b1);

    } else if (ty0 is SetType || ty0 is MapType) {
      Bpl.Expr b0, b1;
      if (ty0 is SetType) {
        Contract.Assert(!((SetType)ty0).Finite);
        b0 = e0;
        b1 = e1;
      } else {
        Contract.Assert(!((MapType)ty0).Finite);
        // for maps, compare their domains as sets
        b0 = FunctionCall(tok, BuiltinFunction.IMapDomain, Predef.MapType, e0);
        b1 = FunctionCall(tok, BuiltinFunction.IMapDomain, Predef.MapType, e1);
      }
      eq = FunctionCall(tok, BuiltinFunction.ISetEqual, null, b0, b1);
      less = Bpl.Expr.False;
      atmost = BplOr(less, eq);

    } else if (ty0 is MultiSetType) {
      eq = FunctionCall(tok, BuiltinFunction.MultiSetEqual, null, e0, e1);
      less = ProperMultiset(tok, e0, e1);
      atmost = FunctionCall(tok, BuiltinFunction.MultiSetSubset, null, e0, e1);

    } else if (ty0 is ArrowType) {
      eq = Bpl.Expr.Eq(e0, e1);
      less = Bpl.Expr.False;  // TODO: try to do better than this
      atmost = BplOr(less, eq);

    } else if (ty0 is BitvectorType) {
      BitvectorType bv = (BitvectorType)ty0;
      eq = Bpl.Expr.Eq(e0, e1);
      less = FunctionCall(tok, "lt_bv" + bv.Width, Bpl.Type.Bool, e0, e1);
      atmost = FunctionCall(tok, "le_bv" + bv.Width, Bpl.Type.Bool, e0, e1);

    } else if (ty0 is BigOrdinalType) {
      eq = Bpl.Expr.Eq(e0, e1);
      less = FunctionCall(tok, "ORD#Less", Bpl.Type.Bool, e0, e1);
      atmost = BplOr(eq, less);

    } else if (ty0.IsTypeParameter || ty0.IsAbstractType) {
      eq = Bpl.Expr.Eq(e0, e1);
      less = Bpl.Expr.False;
      atmost = BplOr(less, eq);

    } else {
      // reference type
      Contract.Assert(ty0.IsRefType);  // otherwise, unexpected type
      var b0 = Bpl.Expr.Neq(e0, Predef.Null);
      var b1 = Bpl.Expr.Neq(e1, Predef.Null);
      eq = BplIff(b0, b1);
      less = BplAnd(Bpl.Expr.Not(b0), b1);
      atmost = BplImp(b0, b1);
    }

    less.tok = tok;
    atmost.tok = tok;
  }
}
