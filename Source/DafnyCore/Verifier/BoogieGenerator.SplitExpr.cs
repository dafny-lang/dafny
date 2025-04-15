//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
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

namespace Microsoft.Dafny {
  public record BodyTranslationContext(bool ContainsHide, int ScopeDepth = 0, bool ReturnPosition = true, AssertMode AssertMode = AssertMode.Keep);

  public partial class BoogieGenerator {
    /// <summary>
    /// Tries to split the expression into tactical conjuncts (if "position") or disjuncts (if "!position").
    /// If a (necessarily boolean) function call appears as a top-level conjunct, then inline the function
    /// if its body is available in the current context and its height is less than "heightLimit" (if "heightLimit" is
    /// passed in as 0, then no functions will be inlined).
    /// </summary>
    bool TrSplitExpr(BodyTranslationContext context, Expression expr, List<SplitExprInfo> splits, /*!*/ /*!*/
      bool position, int heightLimit, bool applyInduction, ExpressionTranslator etran) {
      Contract.Requires(expr != null);
      Contract.Requires(expr.Type.IsBoolType || (expr is BoxingCastExpr && ((BoxingCastExpr)expr).E.Type.IsBoolType));
      Contract.Requires(splits != null);
      Contract.Requires(etran != null);

      switch (expr) {
        case BoxingCastExpr castExpr: {
            var bce = castExpr;
            var ss = new List<SplitExprInfo>();
            if (TrSplitExpr(context, bce.E, ss, position, heightLimit, applyInduction, etran)) {
              foreach (var s in ss) {
                splits.Add(ToSplitExprInfo(s.Kind, CondApplyBox(s.Tok, s.E, bce.FromType, bce.ToType)));
              }
              return true;
            }

            break;
          }
        case ConcreteSyntaxExpression expression: {
            var e = expression;
            return TrSplitExpr(context, e.ResolvedExpression, splits, position, heightLimit, applyInduction, etran);
          }
        case NestedMatchExpr nestedMatchExpr:
          return TrSplitExpr(context, nestedMatchExpr.Flattened, splits, position, heightLimit, applyInduction, etran);
        case LetExpr letExpr: {
            var e = letExpr;
            if (!e.Exact) {
              var d = etran.LetDesugaring(e);
              return TrSplitExpr(context, d, splits, position, heightLimit, applyInduction, etran);
            } else {
              var ss = new List<SplitExprInfo>();
              if (TrSplitExpr(context, e.Body, ss, position, heightLimit, applyInduction, etran)) {
                // We don't know where the RHSs of the let are used in the body. In particular, we don't know if a RHS
                // will end up in a spot where TrSplitExpr would like to increase the Layer offset or not. In fact, different
                // uses of the same let variable may end up needing different Layer constants. The following code will
                // always bump the Layer offset in the RHS. This seems likely to be desireable in many cases, because the
                // LetExpr sits in a position for which TrSplitExpr is invoked.
                List<Bpl.Variable> lhss;
                List<Bpl.Expr> rhss;
                etran.LayerOffset(1).TrLetExprPieces(e, out lhss, out rhss);
                foreach (var s in ss) {
                  // as the source location in the following let, use that of the translated "s"
                  splits.Add(ToSplitExprInfo(s.Kind, new Bpl.LetExpr(s.E.tok, lhss, rhss, null, s.E)));
                }
                return true;
              }
            }

            break;
          }
        case UnchangedExpr unchangedExpr: {
            var e = unchangedExpr;
            if (position && e.Frame.Count > 1) {
              // split into a number of UnchangeExpr's, one for each FrameExpression
              foreach (var fe in e.Frame) {
                var tok = new NestedOrigin(GetToken(e), fe.Origin);
                Expression ee = new UnchangedExpr(tok, [fe], e.At) { AtLabel = e.AtLabel };
                ee.Type = Type.Bool;  // resolve here
                TrSplitExpr(context, ee, splits, position, heightLimit, applyInduction, etran);
              }
              return true;
            }

            break;
          }
        case UnaryOpExpr opExpr: {
            var e = opExpr;
            if (e.ResolvedOp == UnaryOpExpr.ResolvedOpcode.BoolNot) {
              var ss = new List<SplitExprInfo>();
              if (TrSplitExpr(context, e.E, ss, !position, heightLimit, applyInduction, etran)) {
                foreach (var s in ss) {
                  splits.Add(ToSplitExprInfo(s.Kind, Bpl.Expr.Unary(s.E.tok, UnaryOperator.Opcode.Not, s.E)));
                }
                return true;
              }
            }

            break;
          }
        case BinaryExpr binaryExpr: {
            var bin = binaryExpr;
            if (position && bin.ResolvedOp == BinaryExpr.ResolvedOpcode.And) {
              TrSplitExpr(context, bin.E0, splits, position, heightLimit, applyInduction, etran);
              TrSplitExpr(context, bin.E1, splits, position, heightLimit, applyInduction, etran);
              return true;

            } else if (!position && bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Or) {
              TrSplitExpr(context, bin.E0, splits, position, heightLimit, applyInduction, etran);
              TrSplitExpr(context, bin.E1, splits, position, heightLimit, applyInduction, etran);
              return true;

            } else if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Imp) {
              // non-conditionally split these, so we get the source location to point to a subexpression
              if (position) {
                var lhs = etran.TrExpr(bin.E0);
                var ss = new List<SplitExprInfo>();
                TrSplitExpr(context, bin.E1, ss, position, heightLimit, applyInduction, etran);
                foreach (var s in ss) {
                  // as the source location in the following implication, use that of the translated "s"
                  splits.Add(ToSplitExprInfo(s.Kind, Bpl.Expr.Binary(s.E.tok, BinaryOperator.Opcode.Imp, lhs, s.E)));
                }
              } else {
                var ss = new List<SplitExprInfo>();
                TrSplitExpr(context, bin.E0, ss, !position, heightLimit, applyInduction, etran);
                var rhs = etran.TrExpr(bin.E1);
                foreach (var s in ss) {
                  // as the source location in the following implication, use that of the translated "s"
                  splits.Add(ToSplitExprInfo(s.Kind, Bpl.Expr.Binary(s.E.tok, BinaryOperator.Opcode.Imp, s.E, rhs)));
                }
              }
              return true;
            }

            break;
          }
        case TernaryExpr ternaryExpr: {
            var e = ternaryExpr;
            if ((e.Op == TernaryExpr.Opcode.PrefixEqOp && position) || (e.Op == TernaryExpr.Opcode.PrefixNeqOp && !position)) {
              var e1type = e.E1.Type.NormalizeExpand();
              var e2type = e.E2.Type.NormalizeExpand();
              var codecl = e1type.AsCoDatatype;
              Contract.Assert(codecl != null);
              var k = etran.TrExpr(e.E0);
              var A = etran.TrExpr(e.E1);
              var B = etran.TrExpr(e.E2);
              // split as shown here for possibly infinite lists:
              //   checked $PrefixEqual#Dt(k, A, B) || (k_has_successor ==> A.Nil? ==> B.Nil?)
              //   checked $PrefixEqual#Dt(k, A, B) || (k_has_successor ==> A.Cons? ==> B.Cons? && A.head == B.head && $PrefixEqual#2#Dt(k - 1, A.tail, B.tail))  // note the #2 in the recursive call, just like for user-defined predicates that are inlined by TrSplitExpr
              //   checked $PrefixEqual#Dt(k, A, B) || (k != 0 && k.IsLimit ==> $Equal#Dt(A, B))  // (*)
              //   free $PrefixEqual#Dt(k, A, B);
              // Note:  First off, (*) is used only when ORDINAL is involved. Moreover, if there's an error among the first checked
              // conditions, it seems confusing to get yet another error message.  Therefore, we add a middle disjunct to (*), namely
              // the conjunction of all the previous RHSs.
              var kAsORD = !e.E0.Type.IsBigOrdinalType ? FunctionCall(k.tok, "ORD#FromNat", Bpl.Type.Int, k) : k;
              var prefixEqK = CoEqualCall(codecl, e1type.TypeArgs, e2type.TypeArgs, kAsORD, etran.layerInterCluster.LayerN((int)FuelSetting.FuelAmount.HIGH), A, B); // FunctionCall(expr.Tok, CoPrefixName(codecl, 1), Bpl.Type.Bool, k, A, B);
              Bpl.Expr kHasSuccessor, kMinusOne;
              if (e.E0.Type.IsBigOrdinalType) {
                kHasSuccessor = Bpl.Expr.Lt(Bpl.Expr.Literal(0), FunctionCall(k.tok, "ORD#Offset", Bpl.Type.Int, k));
                kMinusOne = FunctionCall(k.tok, "ORD#Minus", Predef.BigOrdinalType, k, FunctionCall(k.tok, "ORD#FromNat", Bpl.Type.Int, Bpl.Expr.Literal(1)));
              } else {
                kHasSuccessor = Bpl.Expr.Lt(Bpl.Expr.Literal(0), k);
                kMinusOne = Bpl.Expr.Sub(k, Bpl.Expr.Literal(1));
                kMinusOne = FunctionCall(k.tok, "ORD#FromNat", Bpl.Type.Int, kMinusOne);
              }
              // for the inlining of the definition of prefix equality, translate the two main equality operands arguments with a higher offset (to obtain #2 functions)
              var etran2 = etran.LayerOffset(1);
              var A2 = etran2.TrExpr(e.E1);
              var B2 = etran2.TrExpr(e.E2);
              var needsTokenAdjust = TrSplitNeedsTokenAdjustment(ternaryExpr);
              var tok = needsTokenAdjust ? new ForceCheckOrigin(ternaryExpr.Origin) : ternaryExpr.Origin;
              Bpl.Expr layer = etran.layerInterCluster.LayerN((int)FuelSetting.FuelAmount.HIGH);
              Bpl.Expr eqComponents = Bpl.Expr.True;
              foreach (var c in CoPrefixEquality(tok, codecl, e1type.TypeArgs, e2type.TypeArgs, kMinusOne, layer, A2, B2, true)) {
                eqComponents = BplAnd(eqComponents, c);
                var p = Bpl.Expr.Binary(c.tok, BinaryOperator.Opcode.Or, prefixEqK, BplImp(kHasSuccessor, c));
                splits.Add(ToSplitExprInfo(SplitExprInfo.K.Checked, p));
              }
              if (e.E0.Type.IsBigOrdinalType) {
                var kIsNonZeroLimit = BplAnd(
                  Bpl.Expr.Neq(k, FunctionCall(k.tok, "ORD#FromNat", Predef.BigOrdinalType, Bpl.Expr.Literal(0))),
                  FunctionCall(k.tok, "ORD#IsLimit", Bpl.Type.Bool, k));
                var eq = CoEqualCall(codecl, e1type.TypeArgs, e2type.TypeArgs, null, etran.layerInterCluster.LayerN((int)FuelSetting.FuelAmount.HIGH), A, B);
                var p = Bpl.Expr.Binary(tok, BinaryOperator.Opcode.Or, prefixEqK, BplOr(BplImp(kHasSuccessor, eqComponents), BplImp(kIsNonZeroLimit, eq)));
                splits.Add(ToSplitExprInfo(SplitExprInfo.K.Checked, p));
              }
              splits.Add(ToSplitExprInfo(SplitExprInfo.K.Free, prefixEqK));
              return true;
            }

            break;
          }
        case ITEExpr iteExpr: {
            var ite = iteExpr;

            var ssThen = new List<SplitExprInfo>();
            var ssElse = new List<SplitExprInfo>();

            TrSplitExpr(context, ite.Thn, ssThen, position, heightLimit, applyInduction, etran);
            TrSplitExpr(context, ite.Els, ssElse, position, heightLimit, applyInduction, etran);

            var op = position ? BinaryOperator.Opcode.Imp : BinaryOperator.Opcode.And;
            var test = etran.TrExpr(ite.Test);
            foreach (var s in ssThen) {
              // as the source location in the following implication, use that of the translated "s"
              splits.Add(ToSplitExprInfo(s.Kind, Bpl.Expr.Binary(s.E.tok, op, test, s.E)));
            }

            var negatedTest = Bpl.Expr.Not(test);
            foreach (var s in ssElse) {
              // as the source location in the following implication, use that of the translated "s"
              splits.Add(ToSplitExprInfo(s.Kind, Bpl.Expr.Binary(s.E.tok, op, negatedTest, s.E)));
            }

            return true;
          }
        case MatchExpr matchExpr: {
            var e = matchExpr;
            var ite = etran.DesugarMatchExpr(e);
            return TrSplitExpr(context, ite, splits, position, heightLimit, applyInduction, etran);
          }
        case StmtExpr stmtExpr: {
            var e = stmtExpr;
            // For an expression S;E in split position, the conclusion of S can be used as an assumption.  Unfortunately,
            // this assumption is not generated in non-split positions (because I don't know how.)
            // So, treat "S; E" like "SConclusion ==> E".
            if (position) {
              var conclusion = etran.TrExpr(e.GetStatementConclusion());
              var ss = new List<SplitExprInfo>();
              TrSplitExpr(context, e.E, ss, position, heightLimit, applyInduction, etran);
              foreach (var s in ss) {
                // as the source location in the following implication, use that of the translated "s"
                splits.Add(ToSplitExprInfo(s.Kind, Bpl.Expr.Binary(s.E.tok, BinaryOperator.Opcode.Imp, conclusion, s.E)));
              }
            } else {
              var ss = new List<SplitExprInfo>();
              TrSplitExpr(context, e.GetStatementConclusion(), ss, !position, heightLimit, applyInduction, etran);
              var rhs = etran.TrExpr(e.E);
              foreach (var s in ss) {
                // as the source location in the following implication, use that of the translated "s"
                splits.Add(ToSplitExprInfo(s.Kind, Bpl.Expr.Binary(s.E.tok, BinaryOperator.Opcode.Imp, s.E, rhs)));
              }
            }
            return true;
          }
        case OldExpr oldExpr: {
            var e = oldExpr;
            return TrSplitExpr(context, e.Expr, splits, position, heightLimit, applyInduction, etran.OldAt(e.AtLabel));
          }
        case FunctionCallExpr callExpr when position: {
            var fexp = callExpr;
            if (TrSplitFunctionCallExpr(context, callExpr, splits, heightLimit, applyInduction, etran, fexp)) {
              return true;
            }

            break;
          }
        case QuantifierExpr quantifierExpr when quantifierExpr.SplitQuantifier != null:
          return TrSplitExpr(context, quantifierExpr.SplitQuantifierExpression, splits, position, heightLimit, applyInduction, etran);
        default: {
            if (((position && expr is ForallExpr) || (!position && expr is ExistsExpr))) {
              var e = (QuantifierExpr)expr;
              var inductionVariables = ApplyInduction(e.BoundVars, e.Attributes);
              if (applyInduction && inductionVariables.Count != 0) {
                // From the given quantifier (forall n :: P(n)), generate the seemingly weaker proof obligation
                //   (forall n :: (forall k :: k < n ==> P(k)) ==> P(n))
                // For an existential (exists n :: P(n)), it is
                //   (exists n :: (forall k :: k < n ==> !P(k)) && P(n))
                //    ^^^^^^                             ^      ^^        <--- note these 3 differences
                var kvars = new List<BoundVar>();
                var kk = new List<Bpl.Expr>();
                var nn = new List<Bpl.Expr>();
                var kkDafny = new List<Expression>();
                var nnDafny = new List<Expression>();
                var toks = new List<IOrigin>();
                var substMap = new Dictionary<IVariable, Expression>();
                foreach (var n in inductionVariables) {
                  toks.Add(n.Origin);
                  BoundVar k = new BoundVar(n.Origin, CurrentIdGenerator.FreshId(n.Name + "$ih#"), n.Type);
                  kvars.Add(k);

                  IdentifierExpr ieK = new IdentifierExpr(k.Origin, k.AssignUniqueName(CurrentDeclaration.IdGenerator));
                  ieK.Var = k; ieK.Type = ieK.Var.Type;  // resolve it here
                  kkDafny.Add(ieK);
                  kk.Add(etran.TrExpr(ieK));

                  IdentifierExpr ieN = new IdentifierExpr(n.Origin, n.AssignUniqueName(CurrentDeclaration.IdGenerator));
                  ieN.Var = n; ieN.Type = ieN.Var.Type;  // resolve it here
                  nnDafny.Add(ieN);
                  nn.Add(etran.TrExpr(ieN));

                  substMap.Add(n, ieK);
                }
                Expression bodyK = Substitute(e.LogicalBody(), null, substMap);
                Bpl.Expr less = DecreasesCheck(toks, null, kkDafny, nnDafny, kk, nn,
                  null, null, false, true);

                Bpl.Expr ihBody = etran.TrExpr(bodyK);
                if (!position) {
                  ihBody = Bpl.Expr.Not(ihBody);
                }
                ihBody = BplAnd(etran.CanCallAssumption(bodyK), ihBody);
                ihBody = BplImp(less, ihBody);
                List<Variable> bvars = [];
                Bpl.Expr typeAntecedent = etran.TrBoundVariables(kvars, bvars);  // no need to use allocation antecedent here, because the well-founded less-than ordering assures kk are allocated
                Bpl.Expr ih;
                var tr = TrTrigger(etran, e.Attributes, expr.Origin, substMap);
                ih = new Bpl.ForallExpr(expr.Origin, bvars, tr, BplImp(typeAntecedent, ihBody));

                // More precisely now:
                //   (forall n :: n-has-expected-type && (forall k :: k < n ==> P(k)) && case0(n)   ==> P(n))
                //   (forall n :: n-has-expected-type && (forall k :: k < n ==> P(k)) && case...(n) ==> P(n))
                // or similar for existentials.
                var caseProduct = new List<Bpl.Expr>() {
                // make sure to include the correct token information (so, don't just use Bpl.Expr.True here)
                new Bpl.LiteralExpr(TrSplitNeedsTokenAdjustment(expr) ? new ForceCheckOrigin(expr.Origin) : expr.Origin, true)
              };
                var i = 0;
                foreach (var n in inductionVariables) {
                  var newCases = new List<Bpl.Expr>();
                  foreach (var kase in InductionCases(n.Type, nn[i], etran)) {
                    foreach (var cs in caseProduct) {
                      if (kase != Bpl.Expr.True) {  // if there's no case, don't add anything to the token
                        newCases.Add(Bpl.Expr.Binary(new NestedOrigin(
                            ToDafnyToken(cs.tok),
                            ToDafnyToken(kase.tok), "datatype constructor"),
                          Bpl.BinaryOperator.Opcode.And, cs, kase));
                      } else {
                        newCases.Add(cs);
                      }
                    }
                  }
                  caseProduct = newCases;
                  i++;
                }
                List<bool> freeOfAlloc = BoundedPool.HasBounds(e.Bounds, BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
                bvars = [];
                typeAntecedent = etran.TrBoundVariables(e.BoundVars, bvars, false, freeOfAlloc);
                foreach (var kase in caseProduct) {
                  var ante = BplAnd(BplAnd(typeAntecedent, ih), kase);
                  var etranBody = etran.LayerOffset(1);
                  var bdy = etranBody.TrExpr(e.LogicalBody());
                  Bpl.Expr q;
                  var trig = TrTrigger(etranBody, e.Attributes, expr.Origin);
                  if (position) {
                    q = new Bpl.ForallExpr(kase.tok, bvars, trig, BplImp(ante, bdy));
                  } else {
                    q = new Bpl.ExistsExpr(kase.tok, bvars, trig, BplAnd(ante, bdy));
                  }
                  splits.Add(ToSplitExprInfo(SplitExprInfo.K.Checked, q));
                }

                // Finally, assume the original quantifier (forall/exists n :: P(n))
                splits.Add(ToSplitExprInfo(SplitExprInfo.K.Free, etran.TrExpr(expr)));
                return true;
              } else {
                // Don't use induction on these quantifiers.
                // Nevertheless, produce two translated versions of the quantifier, one that uses #2 functions (that is, layerOffset 1)
                // for checking and one that uses #1 functions (that is, layerOffset 0) for assuming.
                var etranBoost = etran.LayerOffset(1);
                var r = etranBoost.TrExpr(expr);
                var needsTokenAdjustment = TrSplitNeedsTokenAdjustment(expr);
                if (needsTokenAdjustment) {
                  r.tok = new ForceCheckOrigin(expr.Origin);
                }
                if (etranBoost.Statistics_CustomLayerFunctionCount == 0) {
                  // apparently, the LayerOffset(1) we did had no effect
                  splits.Add(ToSplitExprInfo(SplitExprInfo.K.Both, r));
                  return needsTokenAdjustment;
                } else {
                  splits.Add(ToSplitExprInfo(SplitExprInfo.K.Checked, r));  // check the boosted expression
                  splits.Add(ToSplitExprInfo(SplitExprInfo.K.Free, etran.TrExpr(expr)));  // assume the ordinary expression
                  return true;
                }
              }
            } else if (((position && expr is ExistsExpr) || (!position && expr is ForallExpr))) {
              // produce two translated versions of the quantifier, one that uses #1 functions (that is, layerOffset 0)
              // for checking and one that uses #2 functions (that is, layerOffset 1) for assuming.
              adjustFuelForExists = false; // based on the above comment, we use the etran with correct fuel amount already. No need to adjust anymore.
              var etranBoost = etran.LayerOffset(1);
              var r = etran.TrExpr(expr);
              var needsTokenAdjustment = TrSplitNeedsTokenAdjustment(expr);
              if (needsTokenAdjustment) {
                r.tok = new ForceCheckOrigin(expr.Origin);
              }
              if (etran.Statistics_CustomLayerFunctionCount == 0) {
                // apparently, doesn't use layer
                splits.Add(ToSplitExprInfo(SplitExprInfo.K.Both, r));
                return needsTokenAdjustment;
              } else {
                splits.Add(ToSplitExprInfo(SplitExprInfo.K.Checked, r));  // check the ordinary expression
                splits.Add(ToSplitExprInfo(SplitExprInfo.K.Free, etranBoost.TrExpr(expr)));  // assume the boosted expression
                return true;
              }
            }

            break;
          }
      }

      Bpl.Expr translatedExpression;
      bool splitHappened;
      if ((position && expr is ExistsExpr) || (!position && expr is ForallExpr)) {
        translatedExpression = etran.TrExpr(expr);
        splitHappened = false;
      } else {
        etran = etran.LayerOffset(1);
        translatedExpression = etran.TrExpr(expr);
        splitHappened = etran.Statistics_CustomLayerFunctionCount != 0;  // return true if the LayerOffset(1) came into play
      }
      if (TrSplitNeedsTokenAdjustment(expr)) {
        translatedExpression.tok = new ForceCheckOrigin(expr.Origin);
        splitHappened = true;
      }
      splits.Add(ToSplitExprInfo(SplitExprInfo.K.Both, translatedExpression));
      return splitHappened;
    }


    IEnumerable<Bpl.Expr> InductionCases(Type ty, Bpl.Expr expr, ExpressionTranslator etran) {
      ty = ty.NormalizeExpand();
      IndDatatypeDecl dt = ty.AsIndDatatype;
      if (dt == null) {
        yield return Bpl.Expr.True;
      } else {
        UserDefinedType instantiatedType = (UserDefinedType)ty;  // correctness of cast follows from the non-null return of ty.AsDatatype
        var subst = new Dictionary<TypeParameter, Type>();
        for (int i = 0; i < dt.TypeArgs.Count; i++) {
          subst.Add(dt.TypeArgs[i], instantiatedType.TypeArgs[i]);
        }

        foreach (DatatypeCtor ctor in dt.Ctors) {
          List<Variable> bvs;
          List<Bpl.Expr> args;
          CreateBoundVariables(ctor.Formals, out bvs, out args);
          Bpl.Expr ct = FunctionCall(ctor.Origin, ctor.FullName, Predef.DatatypeType, args);
          // (exists args :: args-have-the-expected-types && ct(args) == expr)
          Bpl.Expr q = Bpl.Expr.Binary(ctor.Origin, BinaryOperator.Opcode.Eq, ct, expr);
          if (bvs.Count != 0) {
            int i = 0;
            Bpl.Expr typeAntecedent = Bpl.Expr.True;
            foreach (Formal arg in ctor.Formals) {
              var instantiatedArgType = arg.Type.Subst(subst);
              Bpl.Expr wh = GetWhereClause(arg.Origin, CondApplyUnbox(arg.Origin, args[i], arg.Type, instantiatedArgType), instantiatedArgType, etran, NOALLOC);
              if (wh != null) {
                typeAntecedent = BplAnd(typeAntecedent, wh);
              }
              i++;
            }
            var trigger = BplTrigger(ct);  // this is probably never used, because this quantifier is not expected ever to appear in a context where it needs to be instantiated
            q = new Bpl.ExistsExpr(ctor.Origin, bvs, trigger, BplAnd(typeAntecedent, q));
          }
          yield return q;
        }
      }
    }

    private bool TrSplitFunctionCallExpr(BodyTranslationContext context,
      Expression expr, List<SplitExprInfo> splits, int heightLimit,
      bool applyInduction, ExpressionTranslator etran, FunctionCallExpr fexp) {
      var f = fexp.Function;
      Contract.Assert(f != null); // filled in during resolution
      var module = f.EnclosingClass.EnclosingModuleDefinition;
      var functionHeight = module.CallGraph.GetSCCRepresentativePredecessorCount(f);

      if (functionHeight < heightLimit && f.Body != null && RevealedInScope(f)) {
        if (fexp.Origin.IsInherited(currentModule) &&
            f is Predicate && ((Predicate)f).BodyOrigin == Predicate.BodyOriginKind.DelayedDefinition &&
            (codeContext == null || !codeContext.MustReverify)) {
          // The function was inherited as body-less but is now given a body. Don't inline the body (since, apparently, everything
          // that needed to be proved about the function was proved already in the previous module, even without the body definition).
        } else if (!FunctionBodyIsAvailable(f, currentModule, currentScope)) {
          // Don't inline opaque functions
        } else if (context.ContainsHide) {
          // Do not inline in a blind context
        } else if (Attributes.Contains(f.Attributes, "no_inline")) {
          // User manually prevented inlining
        } else {
          // Produce, for a "body" split into b0, b1, b2:
          //     checked F#canCall(args) ==> F(args) || b0
          //     checked F#canCall(args) ==> F(args) || b1
          //     checked F#canCall(args) ==> F(args) || b2
          //     free F#canCall(args) && F(args) && (b0 && b1 && b2)
          // For "inCoContext", split into:
          //     checked F#canCall(args) ==> F'(args) || b0''
          //     checked F#canCall(args) ==> F'(args) || b1''
          //     checked F#canCall(args) ==> F'(args) || b2''
          //     free F#canCall(args) && F'(args)
          // where the primes indicate certificate translations.
          // The checked conjuncts of the body make use of the type-specialized body.

          // F#canCall(args)
          Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(expr.Origin, f.FullSanitizedName + "#canCall", Bpl.Type.Bool);
          List<Bpl.Expr> args = etran.FunctionInvocationArguments(fexp, null, null);
          Bpl.Expr canCall = new Bpl.NAryExpr(GetToken(expr), new Bpl.FunctionCall(canCallFuncID), args);

          Bpl.Expr fargs;
          // F(args)
          fargs = etran.TrExpr(fexp);

          if (!CanSafelyInline(fexp, f)) {
            // Skip inlining, as it would cause arbitrary expressions to pop up in the trigger
            // TODO this should appear at the outmost call site, not at the innermost. See SnapshotableTrees.dfy
            reporter.Info(MessageSource.Translator, fexp.Origin, "Some instances of this call are not inlined.");
            // F#canCall(args) ==> F(args)
            var p = Bpl.Expr.Binary(fargs.tok, BinaryOperator.Opcode.Imp, canCall, fargs);
            splits.Add(ToSplitExprInfo(SplitExprInfo.K.Checked, p));
            // F#canCall(args) && F(args)
            var fr = BplAnd(canCall, fargs);
            splits.Add(ToSplitExprInfo(SplitExprInfo.K.Free, fr));
          } else {
            // inline this body
            var typeSpecializedBody = GetSubstitutedBody(fexp, f);
            var typeSpecializedResultType = f.ResultType.Subst(fexp.GetTypeArgumentSubstitutions());

            // recurse on body
            var ss = new List<SplitExprInfo>();
            TrSplitExpr(context, typeSpecializedBody, ss, true, functionHeight, applyInduction, etran);
            var needsTokenAdjust = TrSplitNeedsTokenAdjustment(typeSpecializedBody);
            foreach (var s in ss) {
              if (s.IsChecked) {
                var unboxedConjunct = CondApplyUnbox(s.E.tok, s.E, typeSpecializedResultType, expr.Type);
                var bodyOrConjunct = BplOr(fargs, unboxedConjunct);
                var tok = needsTokenAdjust
                  ? (IOrigin)new ForceCheckOrigin(typeSpecializedBody.Origin)
                  : new NestedOrigin(GetToken(fexp), s.Tok, "this proposition could not be proved");
                var p = Bpl.Expr.Binary(tok, BinaryOperator.Opcode.Imp, canCall, bodyOrConjunct);
                splits.Add(ToSplitExprInfo(SplitExprInfo.K.Checked, p));
              }
            }

            // allocatedness for arguments to the inlined call in body
            if (typeSpecializedBody is FunctionCallExpr) {
              FunctionCallExpr e = (FunctionCallExpr)typeSpecializedBody;
              for (int i = 0; i < e.Args.Count; i++) {
                Expression ee = e.Args[i];
                Type t = e.Function.Ins[i].Type;
                Expr tr_ee = etran.TrExpr(ee);
                Bpl.Expr wh = GetWhereClause(e.Origin, tr_ee, cce.NonNull(ee.Type), etran, NOALLOC);
                if (wh != null) {
                  fargs = BplAnd(fargs, wh);
                }
              }
            }

            // body
            var trBody = etran.TrExpr(typeSpecializedBody);
            trBody = CondApplyUnbox(trBody.tok, trBody, typeSpecializedResultType, expr.Type);
            // F#canCall(args) && F(args) && (b0 && b1 && b2)
            var fr = BplAnd(canCall, BplAnd(fargs, trBody));
            splits.Add(ToSplitExprInfo(SplitExprInfo.K.Free, fr));
          }

          return true;
        }
      }
      return false;
    }


    private bool CanSafelyInline(FunctionCallExpr fexp, Function f) {
      var visitor = new TriggersExplorer();
      if (f.Body != null) {
        var body = f.Body;
        if (f is PrefixPredicate pp) {
          body = PrefixSubstitution(pp, body);
        }
        visitor.Visit(body);
      }
      return
        !triggersCollector.IsTriggerKiller(fexp.Receiver) &&
        Enumerable.Zip(f.Ins, fexp.Args).All(formal_concrete => CanSafelySubstitute(visitor.TriggerVariables, formal_concrete.Item1, formal_concrete.Item2));
    }


    // Using an empty set of old expressions is ok here; the only uses of the triggersCollector will be to check for trigger killers.
    Triggers.TriggersCollector triggersCollector;

    private bool CanSafelySubstitute(ISet<IVariable> protectedVariables, IVariable variable, Expression substitution) {
      return !(protectedVariables.Contains(variable) && triggersCollector.IsTriggerKiller(substitution));
    }

    private class TriggersExplorer : BottomUpVisitor {
      private readonly VariablesCollector collector;

      internal ISet<IVariable> TriggerVariables => collector.variables;

      internal TriggersExplorer() {
        collector = new VariablesCollector();
      }

      protected override void VisitOneExpr(Expression expr) {
        if (expr is QuantifierExpr quantifierExpr && quantifierExpr.SplitQuantifier == null) {
          foreach (var trigger in quantifierExpr.Attributes.AsEnumerable().Where(a => a.Name == "trigger").SelectMany(a => a.Args)) {
            collector.Visit(trigger);
          }
        }
      }
    }

    private Expression GetSubstitutedBody(FunctionCallExpr fexp, Function f) {
      Contract.Requires(fexp != null);
      Contract.Requires(f != null);
      var substMap = new Dictionary<IVariable, Expression>();
      Contract.Assert(fexp.Args.Count == f.Ins.Count);
      for (int i = 0; i < f.Ins.Count; i++) {
        Formal p = f.Ins[i];
        var formalType = p.Type.Subst(fexp.GetTypeArgumentSubstitutions());
        Expression arg = fexp.Args[i];
        arg = new BoxingCastExpr(arg, cce.NonNull(arg.Type), formalType);
        arg.Type = formalType;  // resolve here
        substMap.Add(p, arg);
      }
      var body = f.Body;
      if (f is PrefixPredicate) {
        var pp = (PrefixPredicate)f;
        body = PrefixSubstitution(pp, body);
      }
      body = Substitute(body, fexp.Receiver, substMap, fexp.GetTypeArgumentSubstitutions(), fexp.AtLabel);
      return body;
    }


    SplitExprInfo ToSplitExprInfo(SplitExprInfo.K kind, Expr e) {
      return new SplitExprInfo(flags.ReportRanges, kind, e);
    }

    public class SplitExprInfo {
      public enum K { Free, Checked, Both }
      public K Kind;
      public bool IsOnlyFree { get { return Kind == K.Free; } }
      public bool IsOnlyChecked { get { return Kind == K.Checked; } }
      public bool IsChecked { get { return Kind != K.Free; } }
      public readonly Expr E;
      public IOrigin Tok;
      public SplitExprInfo(bool reportRanges, K kind, Expr e) {
        Contract.Requires(e != null && e.tok != null);
        // TODO:  Contract.Requires(kind == K.Free || e.Tok.IsValid);
        Kind = kind;
        E = e;
        Tok = ToDafnyToken(e.tok);
      }
    }
  }
}
