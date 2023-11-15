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
  void CheckCallTermination(IToken tok, List<Expression> contextDecreases, List<Expression> calleeDecreases,
                            Bpl.Expr allowance,
                            Expression receiverReplacement, Dictionary<IVariable, Expression> substMap,
                            Dictionary<TypeParameter, Type> typeMap,
                            ExpressionTranslator etranCurrent, ExpressionTranslator etranInitial, BoogieStmtListBuilder builder, bool inferredDecreases, string hint) {
    Contract.Requires(tok != null);
    Contract.Requires(cce.NonNullElements(contextDecreases));
    Contract.Requires(cce.NonNullElements(calleeDecreases));
    Contract.Requires(cce.NonNullDictionaryAndValues(substMap));
    Contract.Requires(etranCurrent != null);
    Contract.Requires(etranInitial != null);
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
    var toks = new List<IToken>();
    var types0 = new List<Type>();
    var types1 = new List<Type>();
    var callee = new List<Expr>();
    var caller = new List<Expr>();
    if (RefinementToken.IsInherited(tok, currentModule) && contextDecreases.All(e => !RefinementToken.IsInherited(e.tok, currentModule))) {
      // the call site is inherited but all the context decreases expressions are new
      tok = new ForceCheckToken(tok);
    }
    for (int i = 0; i < N; i++) {
      Expression e0 = Substitute(calleeDecreases[i], receiverReplacement, substMap, typeMap);
      Expression e1 = contextDecreases[i];
      if (!CompatibleDecreasesTypes(e0.Type, e1.Type)) {
        N = i;
        break;
      }
      toks.Add(new NestedToken(tok, e1.tok));
      types0.Add(e0.Type.NormalizeExpand());
      types1.Add(e1.Type.NormalizeExpand());
      callee.Add(etranCurrent.TrExpr(e0));
      caller.Add(etranInitial.TrExpr(e1));
    }
    bool endsWithWinningTopComparison = N == contextDecreases.Count && N < calleeDecreases.Count;
    Bpl.Expr decrExpr = DecreasesCheck(toks, types0, types1, callee, caller, builder, "", endsWithWinningTopComparison, false);
    if (allowance != null) {
      decrExpr = Bpl.Expr.Or(allowance, decrExpr);
    }
    builder.Add(Assert(tok, decrExpr, new PODesc.Terminates(inferredDecreases, false, hint)));
  }

  /// <summary>
  /// Returns the expression that says whether or not the decreases function has gone down (if !allowNoChange)
  /// or has gone down or stayed the same (if allowNoChange).
  /// ee0 represents the new values and ee1 represents old values.
  /// If builder is non-null, then the check '0 ATMOST decr' is generated to builder.
  /// Requires all types in types0 and types1 to be non-proxy non-synonym types (that is, callers should invoke NormalizeExpand)
  /// </summary>
  Bpl.Expr DecreasesCheck(List<IToken> toks, List<Type> types0, List<Type> types1, List<Bpl.Expr> ee0, List<Bpl.Expr> ee1,
                          BoogieStmtListBuilder builder, string suffixMsg, bool allowNoChange, bool includeLowerBound) {
    Contract.Requires(cce.NonNullElements(toks));
    Contract.Requires(cce.NonNullElements(types0));
    Contract.Requires(cce.NonNullElements(types1));
    Contract.Requires(cce.NonNullElements(ee0));
    Contract.Requires(cce.NonNullElements(ee1));
    Contract.Requires(predef != null);
    Contract.Requires(types0.Count == types1.Count && types0.Count == ee0.Count && ee0.Count == ee1.Count);
    Contract.Requires(builder == null || suffixMsg != null);
    Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

    int N = types0.Count;

    // compute eq and less for each component of the lexicographic tuple
    List<Bpl.Expr> Eq = new List<Bpl.Expr>(N);
    List<Bpl.Expr> Less = new List<Bpl.Expr>(N);
    for (int i = 0; i < N; i++) {
      Bpl.Expr less, atmost, eq;
      ComputeLessEq(toks[i], types0[i], types1[i], ee0[i], ee1[i], out less, out atmost, out eq, includeLowerBound);
      Eq.Add(eq);
      Less.Add(allowNoChange ? atmost : less);
    }
    if (builder != null) {
      // check: 0 <= ee1
      // more precisely, for component k of the lexicographic decreases function, check:
      //   ee0[0] < ee1[0] || ee0[1] < ee1[1] || ... || ee0[k-1] < ee1[k-1] || ee0[k] == ee1[k] || 0 <= ee1[k]
      for (int k = 0; k < N; k++) {
        // we only need to check lower bound for integers--sets, sequences, booleans, references, and datatypes all have natural lower bounds
        Bpl.Expr prefixIsLess = Bpl.Expr.False;
        for (int i = 0; i < k; i++) {
          prefixIsLess = Bpl.Expr.Or(prefixIsLess, Less[i]);
        };

        Bpl.Expr zero = null;
        string zeroStr = null;
        if (types0[k].IsNumericBased(Type.NumericPersuasion.Int)) {
          zero = Bpl.Expr.Literal(0);
          zeroStr = "0";
        } else if (types0[k].IsNumericBased(Type.NumericPersuasion.Real)) {
          zero = Bpl.Expr.Literal(BaseTypes.BigDec.ZERO);
          zeroStr = "0.0";
        }
        if (zero != null) {
          Bpl.Expr bounded = Bpl.Expr.Le(zero, ee1[k]);
          for (int i = 0; i < k; i++) {
            bounded = Bpl.Expr.Or(bounded, Less[i]);
          }
          Bpl.Cmd cmd = Assert(toks[k], Bpl.Expr.Or(bounded, Eq[k]), new PODesc.DecreasesBoundedBelow(N, k, zeroStr, suffixMsg));
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
        decrCheck = Bpl.Expr.And(less, Bpl.Expr.Imp(eq, decrCheck));
      } else {
        // decrCheck = less || (eq && decrCheck)
        decrCheck = Bpl.Expr.Or(less, Bpl.Expr.And(eq, decrCheck));
      }
    }
    return decrCheck;
  }

  bool CompatibleDecreasesTypes(Type t, Type u) {
    Contract.Requires(t != null);
    Contract.Requires(u != null);
    t = t.NormalizeExpand();
    u = u.NormalizeExpand();
    if (t is BoolType) {
      return u is BoolType;
    } else if (t is CharType) {
      return u is CharType;
    } else if (t.IsNumericBased(Type.NumericPersuasion.Int)) {
      // we can allow different kinds of int-based types
      return u.IsNumericBased(Type.NumericPersuasion.Int);
    } else if (t.IsNumericBased(Type.NumericPersuasion.Real)) {
      // we can allow different kinds of real-based types
      return u.IsNumericBased(Type.NumericPersuasion.Real);
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
    } else {
      Contract.Assert(t.IsTypeParameter || t.IsAbstractType || t.IsInternalTypeSynonym);
      return false;  // don't consider any type parameters to be the same (since we have no comparison function for them anyway)
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

  void ComputeLessEq(IToken tok, Type ty0, Type ty1, Bpl.Expr e0, Bpl.Expr e1, out Bpl.Expr less, out Bpl.Expr atmost, out Bpl.Expr eq, bool includeLowerBound) {
    Contract.Requires(tok != null);
    Contract.Requires(ty0 != null);
    Contract.Requires(ty1 != null);
    Contract.Requires(e0 != null);
    Contract.Requires(e1 != null);
    Contract.Requires(predef != null);
    Contract.Ensures(Contract.ValueAtReturn(out less) != null);
    Contract.Ensures(Contract.ValueAtReturn(out atmost) != null);
    Contract.Ensures(Contract.ValueAtReturn(out eq) != null);

    ty0 = ty0.NormalizeExpand();
    ty1 = ty1.NormalizeExpand();
    var rk0 = RankFunction(ty0);
    var rk1 = RankFunction(ty1);
    if (rk0 != null && rk1 != null && rk0 != rk1) {
      eq = Bpl.Expr.False;
      Bpl.Expr b0 = FunctionCall(tok, rk0.Value, null, e0);
      Bpl.Expr b1 = FunctionCall(tok, rk1.Value, null, e1);
      less = Bpl.Expr.Lt(b0, b1);
      atmost = Bpl.Expr.Le(b0, b1);
    } else if (ty0 is BoolType) {
      eq = Bpl.Expr.Iff(e0, e1);
      less = Bpl.Expr.And(Bpl.Expr.Not(e0), e1);
      atmost = Bpl.Expr.Imp(e0, e1);
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
        less = Bpl.Expr.And(Bpl.Expr.Le(Bpl.Expr.Literal(0), b0), less);
        atmost = Bpl.Expr.And(Bpl.Expr.Le(Bpl.Expr.Literal(0), b0), atmost);
      }

    } else if (ty0.IsNumericBased(Type.NumericPersuasion.Real)) {
      eq = Bpl.Expr.Eq(e0, e1);
      less = Bpl.Expr.Le(e0, Bpl.Expr.Sub(e1, Bpl.Expr.Literal(BaseTypes.BigDec.FromInt(1))));
      atmost = Bpl.Expr.Le(e0, e1);
      if (includeLowerBound) {
        less = Bpl.Expr.And(Bpl.Expr.Le(Bpl.Expr.Literal(BaseTypes.BigDec.ZERO), e0), less);
        atmost = Bpl.Expr.And(Bpl.Expr.Le(Bpl.Expr.Literal(BaseTypes.BigDec.ZERO), e0), atmost);
      }

    } else if (ty0 is IteratorDecl.EverIncreasingType) {
      eq = Bpl.Expr.Eq(e0, e1);
      less = Bpl.Expr.Gt(e0, e1);
      atmost = Bpl.Expr.Ge(e0, e1);

    } else if ((ty0 is SetType && ((SetType)ty0).Finite) || (ty0 is MapType && ((MapType)ty0).Finite)) {
      Bpl.Expr b0, b1;
      if (ty0 is SetType) {
        b0 = e0;
        b1 = e1;
      } else {
        // for maps, compare their domains as sets
        b0 = FunctionCall(tok, BuiltinFunction.MapDomain, predef.MapType, e0);
        b1 = FunctionCall(tok, BuiltinFunction.MapDomain, predef.MapType, e1);
      }
      eq = FunctionCall(tok, BuiltinFunction.SetEqual, null, b0, b1);
      less = ProperSubset(tok, b0, b1);
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
        b0 = FunctionCall(tok, BuiltinFunction.IMapDomain, predef.MapType, e0);
        b1 = FunctionCall(tok, BuiltinFunction.IMapDomain, predef.MapType, e1);
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
      var b0 = Bpl.Expr.Neq(e0, predef.Null);
      var b1 = Bpl.Expr.Neq(e1, predef.Null);
      eq = Bpl.Expr.Iff(b0, b1);
      less = Bpl.Expr.And(Bpl.Expr.Not(b0), b1);
      atmost = Bpl.Expr.Imp(b0, b1);
    }
  }
}