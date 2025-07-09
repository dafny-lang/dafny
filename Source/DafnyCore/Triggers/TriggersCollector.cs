// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny.Triggers;

internal class TriggersCollector {
  public ModuleDefinition ForModule { get; }
  private readonly DafnyOptions options;
  private readonly TriggerAnnotationsCache cache;

  internal TriggersCollector(Dictionary<Expression, HashSet<OldExpr>> exprsInOldContext, DafnyOptions options, ModuleDefinition forModule) {
    this.options = options;
    this.ForModule = forModule;
    this.cache = new TriggerAnnotationsCache(exprsInOldContext);
  }

  private T ReduceAnnotatedSubExpressions<T>(Expression expr, T seed, Func<TriggerAnnotation, T> map, Func<T, T, T> reduce) {
    return expr.SubExpressions.Select(e => map(Annotate(e)))
      .Aggregate(seed, reduce);
  }

  private List<TriggerTerm> CollectExportedCandidates(Expression expr) {
    return ReduceAnnotatedSubExpressions(expr, [], a => a.ExportedTerms, TriggerUtils.MergeAlterFirst);
  }

  private ISet<IVariable> CollectVariables(Expression expr) {
    return ReduceAnnotatedSubExpressions<ISet<IVariable>>(expr, new HashSet<IVariable>(), a => a.Variables, TriggerUtils.MergeAlterFirst);
  }

  private bool CollectIsKiller(Expression expr) {
    return ReduceAnnotatedSubExpressions(expr, false, a => a.IsTriggerKiller, (a, b) => a || b);
  }

  private IEnumerable<TriggerTerm> OnlyPrivateCandidates(List<TriggerTerm> terms, IEnumerable<IVariable> privateVars) {
    return terms.Where(c => privateVars.Intersect(c.Variables).Any()); //TODO Check perf
  }

  private TriggerAnnotation Annotate(Expression expr) {
    if (cache.Annotations.TryGetValue(expr, out var cached)) {
      return cached;
    }

    TriggerAnnotation annotation = null; // TODO: Using ApplySuffix fixes the unresolved members problem in GenericSort

    if (expr is LetExpr { Exact: true } letExpr && letExpr.LHSs.All(p => p.Var != null)) {
      // Inline the let expression before doing trigger selection.
      annotation = Annotate(BoogieGenerator.InlineLet(letExpr));
    }

    if (annotation == null) {
      expr.SubExpressions.ForEach(e => Annotate(e));

      if (IsPotentialTriggerCandidate(expr)) {
        annotation = AnnotatePotentialCandidate(expr);
      } else if (expr is QuantifierExpr) {
        annotation = AnnotateQuantifier((QuantifierExpr)expr);
      } else if (expr is LetExpr) {
        annotation = AnnotateLetExpr((LetExpr)expr);
      } else if (expr is IdentifierExpr) {
        annotation = AnnotateIdentifier((IdentifierExpr)expr);
      } else if (expr is ApplySuffix) {
        annotation = AnnotateApplySuffix((ApplySuffix)expr);
      } else if (expr is MatchExpr) {
        annotation = AnnotateMatchExpr((MatchExpr)expr);
      } else if (expr is NestedMatchExpr nestedMatchExpr) {
        annotation = AnnotateNestedMatchExpr(nestedMatchExpr);
      } else if (expr is ComprehensionExpr) {
        annotation = AnnotateComprehensionExpr((ComprehensionExpr)expr);
      } else if (expr is ConcreteSyntaxExpression ||
                 expr is LiteralExpr ||
                 expr is ThisExpr ||
                 expr is BoxingCastExpr ||
                 expr is MultiSetFormingExpr ||
                 expr is SeqConstructionExpr) {
        annotation = AnnotateOther(expr, false);
      } else {
        annotation = AnnotateOther(expr, true);
      }
    }

    cache.Annotations[expr] = annotation;
    return annotation;
  }

  public bool IsPotentialTriggerCandidate(Expression expr) {
    if (expr is FunctionCallExpr ||
        expr is SeqSelectExpr ||
        expr is MultiSelectExpr ||
        expr is MemberSelectExpr ||
        (expr is OldExpr { Useless: false }) ||
        expr is ApplyExpr ||
        expr is DisplayExpression ||
        expr is MapDisplayExpr ||
        expr is DatatypeValue ||
        expr is TernaryExpr ||
        TranslateToFunctionCall(expr)) {
      return true;
    } else if (expr is BinaryExpr) {
      var e = (BinaryExpr)expr;
      if ((e.Op == BinaryExpr.Opcode.NotIn || e.Op == BinaryExpr.Opcode.In) && !BoogieGenerator.ExpressionTranslator.RewriteInExpr(e.E1, false)) {
        return true;
      } else if (CandidateCollectionOperation(e)) {
        return true;
      } else if (e.E0.Type.IsBigOrdinalType &&
                 (e.ResolvedOp == BinaryExpr.ResolvedOpcode.Lt || e.ResolvedOp == BinaryExpr.ResolvedOpcode.LessThanLimit || e.ResolvedOp == BinaryExpr.ResolvedOpcode.Gt)) {
        return true;
      } else {
        return false;
      }
    } else if (expr is UnaryOpExpr) {
      var e = (UnaryOpExpr)expr;
      return e.Op == UnaryOpExpr.Opcode.Cardinality;  // FIXME || e.Op == UnaryOpExpr.Opcode.Fresh doesn't work, as fresh is a pretty tricky predicate when it's not about datatypes. See translator.cs:10944
    } else if (expr is ConversionExpr) {
      var e = (ConversionExpr)expr;
      return e.ToType.IsBigOrdinalType;
    } else {
      return false;
    }
  }

  // math operations can be turned into a Boogie-level function as in the
  // case with /noNLarith.
  public bool TranslateToFunctionCall(Expression expr) {
    if (!(expr is BinaryExpr)) {
      return false;
    }
    BinaryExpr e = (BinaryExpr)expr;
    bool isReal = e.E0.Type.IsNumericBased(Type.NumericPersuasion.Real);
    var disableNonLinearArithmetic = BoogieGenerator.DetermineDisableNonLinearArithmetic(ForModule, options);
    switch (e.ResolvedOp) {
      case BinaryExpr.ResolvedOpcode.Lt:
      case BinaryExpr.ResolvedOpcode.Le:
      case BinaryExpr.ResolvedOpcode.Ge:
      case BinaryExpr.ResolvedOpcode.Gt:
      case BinaryExpr.ResolvedOpcode.Add:
      case BinaryExpr.ResolvedOpcode.Sub:
        if (!isReal && !e.E0.Type.IsBitVectorType && !e.E0.Type.IsBigOrdinalType && disableNonLinearArithmetic) {
          return true;
        }
        break;
      case BinaryExpr.ResolvedOpcode.Mul:
      case BinaryExpr.ResolvedOpcode.Div:
      case BinaryExpr.ResolvedOpcode.Mod:
        if (!isReal && !e.E0.Type.IsBitVectorType && !e.E0.Type.IsBigOrdinalType) {
          if (disableNonLinearArithmetic || (options.ArithMode != 0 && options.ArithMode != 3)) {
            return true;
          }
        }
        break;
    }
    return false;
  }

  static bool CandidateCollectionOperation(BinaryExpr binExpr) {
    Contract.Requires(binExpr != null);
    var type = binExpr.E0.Type.AsCollectionType;
    if (type == null) {
      return false;
    }
    if (type is SetType) {
      switch (binExpr.ResolvedOp) {
        case BinaryExpr.ResolvedOpcode.Union:
        case BinaryExpr.ResolvedOpcode.Intersection:
        case BinaryExpr.ResolvedOpcode.SetDifference:
        case BinaryExpr.ResolvedOpcode.ProperSubset:
        case BinaryExpr.ResolvedOpcode.Subset:
        case BinaryExpr.ResolvedOpcode.Superset:
        case BinaryExpr.ResolvedOpcode.ProperSuperset:
          return true;
      }
    } else if (type is MultiSetType) {
      switch (binExpr.ResolvedOp) {
        case BinaryExpr.ResolvedOpcode.MultiSetUnion:
        case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
        case BinaryExpr.ResolvedOpcode.MultiSetDifference:
        case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
        case BinaryExpr.ResolvedOpcode.MultiSubset:
        case BinaryExpr.ResolvedOpcode.MultiSuperset:
        case BinaryExpr.ResolvedOpcode.ProperMultiSuperset:
          return true;
      }
    } else if (type is SeqType) {
      switch (binExpr.ResolvedOp) {
        case BinaryExpr.ResolvedOpcode.Concat:
          return true;
      }
    } else if (type is MapType) {
      switch (binExpr.ResolvedOp) {
        case BinaryExpr.ResolvedOpcode.MapMerge:
        case BinaryExpr.ResolvedOpcode.MapSubtraction:
          return true;
      }
    }
    return false;
  }

  private TriggerAnnotation AnnotatePotentialCandidate(Expression expr) {
    var oldExprSet = cache.ExpressionsInOldContext.GetValueOrDefault(expr);
    // oldExpr has been set to the value found
    var newExpressions = TriggerUtils.MaybeWrapInOld(PrepareExprForInclusionInTrigger(expr, out var exprIsKiller), oldExprSet);
    // We expect there to be at least one "newExpressions".
    // We also expect that the computation of new_term.Variables, collected_terms, and children_contain_killers will be the
    // same for each of the "new_exprs".
    // Therefore, we use the values of these variables from the last iteration in the expression that is ultimately returned.
    TriggerTerm newTerm = null;
    List<TriggerTerm> collectedTerms = null;
    var childrenContainKillers = false;
    foreach (var newExpression in newExpressions) {
      newTerm = new TriggerTerm { Expr = newExpression, OriginalExpr = expr, Variables = CollectVariables(expr) };

      collectedTerms = CollectExportedCandidates(expr);
      childrenContainKillers = CollectIsKiller(expr);

      if (!childrenContainKillers) {
        // Add only if the children are not killers; the head has been cleaned up into non-killer form
        collectedTerms.Add(newTerm);
      }
    }
    Contract.Assert(newTerm != null);  // this checks our assumption that "new_exprs" contains at least one value.

    // This new node is a killer if its children were killers, or if it's non-cleaned-up head is a killer
    return new TriggerAnnotation(childrenContainKillers || exprIsKiller, newTerm.Variables, collectedTerms);
  }

  private TriggerAnnotation AnnotateApplySuffix(ApplySuffix expr) {
    // This is a bit tricky. A funcall node is generally meaningful as a trigger candidate,
    // but when it's part of an ApplySuffix the function call itself may not resolve properly
    // when the second round of resolving is done after modules are duplicated.
    // Thus first we annotate expr and create a trigger candidate, and then we remove the
    // candidate matching its direct subexpression if needed. Note that function calls are not the
    // only possible child here; there can be DatatypeValue nodes, for example (see vstte2012/Combinators.dfy).
    var annotation = AnnotatePotentialCandidate(expr);
    // Comparing by reference is fine here. Using sets could yield a small speedup
    annotation.ExportedTerms.RemoveAll(term => expr.SubExpressions.Contains(term.Expr));
    return annotation;
  }

  private TriggerAnnotation AnnotateQuantifierOrLetExpr(Expression expr, IEnumerable<BoundVar> boundVars) {
    var terms = CollectExportedCandidates(expr);
    return new TriggerAnnotation(true, CollectVariables(expr), terms, OnlyPrivateCandidates(terms, boundVars));
  }

  private TriggerAnnotation AnnotateQuantifier(QuantifierExpr expr) {
    return AnnotateQuantifierOrLetExpr(expr, expr.BoundVars);
  }

  private TriggerAnnotation AnnotateLetExpr(LetExpr expr) {
    return AnnotateQuantifierOrLetExpr(expr, expr.BoundVars);
  }

  private TriggerAnnotation AnnotateIdentifier(IdentifierExpr expr) {
    return new TriggerAnnotation(false, Enumerable.Repeat(expr.Var, 1), null);
  }

  private TriggerAnnotation AnnotateComprehensionExpr(ComprehensionExpr expr) {
    var terms = CollectExportedCandidates(expr);
    return new TriggerAnnotation(true, CollectVariables(expr), terms, OnlyPrivateCandidates(terms, expr.BoundVars));
  }

  private TriggerAnnotation AnnotateNestedMatchExpr(NestedMatchExpr expr) {
    var candidateTerms = CollectExportedCandidates(expr);
    // collects that argument boundvar of matchcaseexpr
    var variables = expr.Cases.SelectMany(e => e.Pat.DescendantsAndSelf).
      OfType<IdPattern>().Select(id => id.BoundVar).Where(b => b != null).ToList();
    // remove terms that mentions argument boundvar of matchcaseexpr
    var terms = candidateTerms.Where(term => variables.Any(x => !term.Variables.Contains(x))).ToList();
    return new TriggerAnnotation(true, CollectVariables(expr), terms);
  }

  private TriggerAnnotation AnnotateMatchExpr(MatchExpr expr) {
    var pts = CollectExportedCandidates(expr);
    // collects that argument boundvar of matchcaseexpr
    var variables = expr.Cases.Select(e => e.Arguments).
      Aggregate(new List<BoundVar>(), (acc, e) => TriggerUtils.MergeAlterFirst(acc, e));
    // remove terms that mentions argument boundvar of matchcaseexpr
    var terms = new List<TriggerTerm>();
    foreach (var term in pts) {
      if (!(variables.All(x => term.Variables.Contains(x)))) {
        terms.Add(term);
      }
    }
    return new TriggerAnnotation(true, CollectVariables(expr), terms);
  }

  private TriggerAnnotation AnnotateOther(Expression expr, bool isTriggerKiller) {
    return new TriggerAnnotation(isTriggerKiller || CollectIsKiller(expr), CollectVariables(expr), CollectExportedCandidates(expr));
  }

  /// <summary>
  /// Collect terms in the body of the subexpressions of the argument that look like quantifiers. The results of this function can contain duplicate terms.
  /// </summary>
  internal List<TriggerTerm> CollectTriggers(ComprehensionExpr quantifier) {
    Contract.Requires(!(quantifier is QuantifierExpr) || ((QuantifierExpr)quantifier).SplitQuantifier == null); // Don't call this on a quantifier with a Split clause: it's not a real quantifier
    // NOTE: We could check for existing trigger attributes and return that instead
    return Annotate(quantifier).PrivateTerms;
  }

  internal bool IsTriggerKiller(Expression expr) {
    return Annotate(expr).IsTriggerKiller;
  }

  internal static Expression PrepareExprForInclusionInTrigger(Expression expr) {
    return PrepareExprForInclusionInTrigger(expr, out var @_);
  }

  private static Expression PrepareExprForInclusionInTrigger(Expression expr, out bool isKiller) {
    isKiller = false;

    Expression ret;
    do {
      ret = expr;
      if (expr is BinaryExpr bin) {
        if (bin.Op == BinaryExpr.Opcode.NotIn) {
          expr = new BinaryExpr(bin.Origin, BinaryExpr.Opcode.In, bin.E0, bin.E1) {
            ResolvedOp = RemoveNotInBinaryExprIn(bin.ResolvedOp),
            Type = bin.Type
          };
        } else if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.InMultiSet) {
          expr = new SeqSelectExpr(bin.Origin, true, bin.E1, bin.E0, null, null) {
            Type = bin.Type
          };
          isKiller = true; // [a in s] becomes [s[a] > 0], which is a trigger killer
        } else {
          var newOpcode = ChangeProperToInclusiveContainment(bin.ResolvedOp);
          if (newOpcode != bin.ResolvedOp) {
            // For sets, isets, and multisets, change < to <= in triggers (and analogously
            // > to >=), since "a < b" translates as "a <= b && !(b <= a)" or
            // "a <= b && !(a == b)".
            expr = new BinaryExpr(bin.Origin, BinaryExpr.ResolvedOp2SyntacticOp(newOpcode), bin.E0, bin.E1) {
              ResolvedOp = newOpcode,
              Type = bin.Type
            };
          }
        }
      }
    } while (ret != expr);

    return ret;
  }
  private static BinaryExpr.ResolvedOpcode RemoveNotInBinaryExprIn(BinaryExpr.ResolvedOpcode opcode) {
    switch (opcode) {
      case BinaryExpr.ResolvedOpcode.NotInMap:
        return BinaryExpr.ResolvedOpcode.InMap;
      case BinaryExpr.ResolvedOpcode.NotInSet:
        return BinaryExpr.ResolvedOpcode.InSet;
      case BinaryExpr.ResolvedOpcode.NotInSeq:
        return BinaryExpr.ResolvedOpcode.InSeq;
      case BinaryExpr.ResolvedOpcode.NotInMultiSet:
        return BinaryExpr.ResolvedOpcode.InMultiSet;
    }

    Contract.Assert(false);
    throw new ArgumentException();
  }

  private static BinaryExpr.ResolvedOpcode ChangeProperToInclusiveContainment(BinaryExpr.ResolvedOpcode opcode) {
    return opcode switch {
      BinaryExpr.ResolvedOpcode.ProperSubset => BinaryExpr.ResolvedOpcode.Subset,
      BinaryExpr.ResolvedOpcode.ProperMultiSubset => BinaryExpr.ResolvedOpcode.MultiSubset,
      BinaryExpr.ResolvedOpcode.ProperSuperset => BinaryExpr.ResolvedOpcode.Superset,
      BinaryExpr.ResolvedOpcode.ProperMultiSuperset => BinaryExpr.ResolvedOpcode.MultiSuperset,
      _ => opcode
    };
  }
}