using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

class FillInDefaultLoopDecreasesVisitor : ResolverBottomUpVisitor {
  readonly ICallable EnclosingMethod;
  public FillInDefaultLoopDecreasesVisitor(ModuleResolver resolver, ICallable enclosingMethod)
    : base(resolver) {
    Contract.Requires(resolver != null);
    Contract.Requires(enclosingMethod != null);
    EnclosingMethod = enclosingMethod;
  }
  protected override void VisitOneStmt(Statement stmt) {
    if (stmt is WhileStmt) {
      var s = (WhileStmt)stmt;
      FillInDefaultLoopDecreases(resolver, s, s.Guard, s.Decreases.Expressions, EnclosingMethod);
    } else if (stmt is AlternativeLoopStmt) {
      var s = (AlternativeLoopStmt)stmt;
      FillInDefaultLoopDecreases(resolver, s, null, s.Decreases.Expressions, EnclosingMethod);
    }
  }

  private static void FillInDefaultLoopDecreases(ModuleResolver resolver, LoopStmt loopStmt, Expression guard, List<Expression> theDecreases, ICallable enclosingMethod) {
    Contract.Requires(loopStmt != null);
    Contract.Requires(theDecreases != null);

    if (theDecreases.Count == 0 && guard != null) {
      loopStmt.InferredDecreases = true;
      Expression prefix = null;
      foreach (Expression guardConjunct in Expression.Conjuncts(guard)) {
        Expression guess = null;
        var neutralValue = Expression.CreateIntLiteral(guardConjunct.Origin, -1);
        if (guardConjunct is BinaryExpr bin) {
          switch (bin.ResolvedOp) {
            case BinaryExpr.ResolvedOpcode.Lt:
            case BinaryExpr.ResolvedOpcode.Le:
            case BinaryExpr.ResolvedOpcode.LtChar:
            case BinaryExpr.ResolvedOpcode.LeChar:
              if (bin.E0.Type.IsBigOrdinalType) {
                // we can't rely on subtracting ORDINALs, so let's just pick the upper bound and hope that works
                guess = bin.E1;
              } else {
                // for A < B and A <= B, use the decreases B - A
                guess = Expression.CreateSubtract_TypeConvert(bin.E1, bin.E0);
              }
              break;
            case BinaryExpr.ResolvedOpcode.Ge:
            case BinaryExpr.ResolvedOpcode.Gt:
            case BinaryExpr.ResolvedOpcode.GeChar:
            case BinaryExpr.ResolvedOpcode.GtChar:
              if (bin.E0.Type.IsBigOrdinalType) {
                // we can't rely on subtracting ORDINALs, so let's just pick the upper bound and hope that works
                guess = bin.E0;
              } else {
                // for A >= B and A > B, use the decreases A - B
                guess = Expression.CreateSubtract_TypeConvert(bin.E0, bin.E1);
              }
              break;
            case BinaryExpr.ResolvedOpcode.ProperSubset:
            case BinaryExpr.ResolvedOpcode.Subset:
              if (bin.E0.Type.AsSetType.Finite) {
                // for A < B and A <= B, use the decreases |B - A|
                guess = Expression.CreateCardinality(Expression.CreateSetDifference(bin.E1, bin.E0), resolver.SystemModuleManager);
              }
              break;
            case BinaryExpr.ResolvedOpcode.Superset:
            case BinaryExpr.ResolvedOpcode.ProperSuperset:
              if (bin.E0.Type.AsSetType.Finite) {
                // for A >= B and A > B, use the decreases |A - B|
                guess = Expression.CreateCardinality(Expression.CreateSetDifference(bin.E0, bin.E1), resolver.SystemModuleManager);
              }
              break;
            case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
            case BinaryExpr.ResolvedOpcode.MultiSubset:
              // for A < B and A <= B, use the decreases |B - A|
              guess = Expression.CreateCardinality(Expression.CreateMultisetDifference(bin.E1, bin.E0), resolver.SystemModuleManager);
              break;
            case BinaryExpr.ResolvedOpcode.MultiSuperset:
            case BinaryExpr.ResolvedOpcode.ProperMultiSuperset:
              // for A >= B and A > B, use the decreases |A - B|
              guess = Expression.CreateCardinality(Expression.CreateMultisetDifference(bin.E0, bin.E1), resolver.SystemModuleManager);
              break;
            case BinaryExpr.ResolvedOpcode.Prefix:
            case BinaryExpr.ResolvedOpcode.ProperPrefix:
              // for "[] < B" and "[] <= B", use B
              if (LiteralExpr.IsEmptySequence(bin.E0)) {
                guess = bin.E1;
              }
              break;
            case BinaryExpr.ResolvedOpcode.NeqCommon:
              if (bin.E0.Type.IsNumericBased() || bin.E0.Type.IsBitVectorType || bin.E0.Type.IsCharType) {
                // for A != B where A and B are numeric, use the absolute difference between A and B (that is: if A <= B then B-A else A-B)
                var AminusB = Expression.CreateSubtract_TypeConvert(bin.E0, bin.E1);
                var BminusA = Expression.CreateSubtract_TypeConvert(bin.E1, bin.E0);
                var test = Expression.CreateAtMost(bin.E0, bin.E1);
                guess = Expression.CreateITE(test, BminusA, AminusB);
              } else if (bin.E0.Type.IsBigOrdinalType) {
                // if either of the operands is a literal, pick the other; otherwise, don't make any guess
                if (Expression.StripParens(bin.E0) is LiteralExpr) {
                  guess = bin.E1;
                } else if (Expression.StripParens(bin.E1) is LiteralExpr) {
                  guess = bin.E0;
                }
              }
              break;
            case BinaryExpr.ResolvedOpcode.SetNeq:
              if (bin.E0.Type.AsSetType.Finite) {
                // use |A - B| + |B - A|, but specialize it for the case where A or B is the empty set
                if (LiteralExpr.IsEmptySet(bin.E0)) {
                  guess = bin.E1;
                } else if (LiteralExpr.IsEmptySet(bin.E1)) {
                  guess = bin.E0;
                } else {
                  var x = Expression.CreateCardinality(Expression.CreateSetDifference(bin.E0, bin.E1), resolver.SystemModuleManager);
                  var y = Expression.CreateCardinality(Expression.CreateSetDifference(bin.E1, bin.E0), resolver.SystemModuleManager);
                  guess = Expression.CreateAdd(x, y);
                }
              }
              break;
            case BinaryExpr.ResolvedOpcode.MultiSetNeq:
              // use |A - B| + |B - A|, but specialize it for the case where A or B is the empty multiset
              if (LiteralExpr.IsEmptyMultiset(bin.E0)) {
                guess = bin.E1;
              } else if (LiteralExpr.IsEmptyMultiset(bin.E1)) {
                guess = bin.E0;
              } else {
                var x = Expression.CreateCardinality(Expression.CreateMultisetDifference(bin.E0, bin.E1), resolver.SystemModuleManager);
                var y = Expression.CreateCardinality(Expression.CreateMultisetDifference(bin.E1, bin.E0), resolver.SystemModuleManager);
                guess = Expression.CreateAdd(x, y);
              }
              break;
            case BinaryExpr.ResolvedOpcode.SeqNeq:
              // if either operand is [], then use the other
              if (LiteralExpr.IsEmptySequence(bin.E0)) {
                guess = bin.E1;
              } else if (LiteralExpr.IsEmptySequence(bin.E1)) {
                guess = bin.E0;
              }
              break;
            default:
              break;
          }
          if (bin.E0.Type.AsSetType != null) {
            neutralValue = new SetDisplayExpr(bin.Origin, bin.E0.Type.AsSetType.Finite, []) {
              Type = bin.E0.Type.NormalizeExpand()
            };
          } else if (bin.E0.Type.AsMultiSetType != null) {
            neutralValue = new MultiSetDisplayExpr(bin.Origin, []) {
              Type = bin.E0.Type.NormalizeExpand()
            };
          } else if (bin.E0.Type.AsSeqType != null) {
            neutralValue = new SeqDisplayExpr(bin.Origin, []) {
              Type = bin.E0.Type.NormalizeExpand()
            };
          } else if (bin.E0.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
            neutralValue = Expression.CreateRealLiteral(bin.Origin, BaseTypes.BigDec.FromInt(-1));
          }
        }
        if (guess != null) {
          if (prefix != null) {
            // Make the following guess:  if prefix then guess else neutralValue
            guess = Expression.CreateITE(prefix, guess, neutralValue);
          }
          theDecreases.Add(AutoGeneratedExpression.Create(guess));
        }
        if (prefix == null) {
          prefix = guardConjunct;
        } else {
          prefix = Expression.CreateAnd(prefix, guardConjunct);
        }
      }
    }
    if (enclosingMethod is IteratorDecl) {
      var iter = (IteratorDecl)enclosingMethod;
      var ie = new IdentifierExpr(loopStmt.Origin, iter.YieldCountVariable.Name);
      ie.Var = iter.YieldCountVariable;  // resolve here
      ie.Type = iter.YieldCountVariable.Type;  // resolve here
      theDecreases.Insert(0, AutoGeneratedExpression.Create(ie));
      loopStmt.InferredDecreases = true;
    }
    if (loopStmt.InferredDecreases && theDecreases.Count != 0) {
      string s = "decreases " + Util.Comma(theDecreases, expr => Printer.ExprToString(resolver.Options, expr));
      resolver.reporter.Info(MessageSource.Resolver, loopStmt.Origin, s);
    }
  }
}