//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny {
  public partial class ModuleResolver {
    private class BoundsDiscoveryVisitor : ASTVisitor<BoundsDiscoveryVisitor.BoundsDiscoveryContext> {
      private readonly ModuleResolver resolver;

      public class BoundsDiscoveryContext : IASTVisitorContext {
        private readonly IASTVisitorContext astVisitorContext;
        readonly bool inLambdaExpression;

        public bool AllowedToDependOnAllocationState =>
          !(astVisitorContext is Function or ConstantField or RedirectingTypeDecl || inLambdaExpression);

        public string Kind {
          get {
            // assumes context denotes a lambda expression, redirecting type, or member declaration
            if (inLambdaExpression) {
              return "lambda expression";
            }
            string kind;
            if (astVisitorContext is RedirectingTypeDecl redirectingTypeDecl) {
              kind = redirectingTypeDecl.WhatKind;
            } else {
              var memberDecl = (MemberDecl)astVisitorContext;
              kind = memberDecl.WhatKind;
            }
            return $"{kind} definition";
          }
        }

        public BoundsDiscoveryContext(IASTVisitorContext astVisitorContext) {
          this.astVisitorContext = astVisitorContext;
          this.inLambdaExpression = false;
        }

        /// <summary>
        /// This constructor is used to say that, within parentContext, the context is inside a lambda
        /// expression.
        /// </summary>
        public BoundsDiscoveryContext(BoundsDiscoveryContext parentContext, LambdaExpr lambdaExpr) {
          this.astVisitorContext = parentContext.astVisitorContext;
          this.inLambdaExpression = true;
        }

        ModuleDefinition IASTVisitorContext.EnclosingModule => astVisitorContext.EnclosingModule;
      }

      private ErrorReporter Reporter => resolver.Reporter;

      public BoundsDiscoveryVisitor(ModuleResolver resolver) {
        this.resolver = resolver;
      }

      public override BoundsDiscoveryContext GetContext(IASTVisitorContext astVisitorContext, bool inFunctionPostcondition) {
        return new BoundsDiscoveryContext(astVisitorContext);
      }

      protected override bool VisitOneStatement(Statement stmt, BoundsDiscoveryContext context) {
        if (stmt is ForallStmt forallStmt) {
          forallStmt.Bounds = DiscoverBestBounds_MultipleVars(forallStmt.BoundVars, forallStmt.Range, true);
          if (forallStmt.Body == null) {
            Reporter.Warning(MessageSource.Resolver, ErrorRegistry.NoneId, forallStmt.Origin, "this forall statement has no body");
          }
        } else if (stmt is AssignSuchThatStmt assignSuchThatStmt) {
          if (assignSuchThatStmt.AssumeToken == null) {
            var varLhss = new List<IVariable>();
            foreach (var lhs in assignSuchThatStmt.Lhss) {
              var ide = (IdentifierExpr)lhs.Resolved;  // successful resolution implies all LHS's are IdentifierExpr's
              varLhss.Add(ide.Var);
            }
            assignSuchThatStmt.Bounds = DiscoverBestBounds_MultipleVars(varLhss, assignSuchThatStmt.Expr, true);
          }
        } else if (stmt is OneBodyLoopStmt oneBodyLoopStmt) {
          oneBodyLoopStmt.ComputeBodySurrogate(Reporter);
        }

        return base.VisitOneStatement(stmt, context);
      }

      public override void VisitTopLevelFrameExpression(FrameExpression frameExpression, BoundsDiscoveryContext context) {
        DesugarFunctionsInFrameClause(frameExpression);
        base.VisitTopLevelFrameExpression(frameExpression, context);
      }

      void DesugarFunctionsInFrameClause(FrameExpression frameExpression) {
        frameExpression.DesugaredExpression = FrameArrowToObjectSet(frameExpression.E);
      }

      /// <summary>
      /// The motivation for this method is to convert a reads-clause frame expression "f.reads" into a set.
      /// More generally, if the given expression "e" has type "X ~> collection<Y>", for some list of type X,
      /// some reference type Y, and "collection" being "set", "iset", "seq", or "multiset", then this method
      /// returns an expression of type "set<Y>" denoting
      ///
      ///     UNION x: X :: e(x)                      // e.g., UNION x: X :: f.reads(x)
      ///
      /// For example, if "e" is an expression "f.reads" of type "X ~> set<object>", then the expression
      /// returned is the union of "f.reads(x)" over all inputs "x" to "f".
      ///
      /// If the type of "e" is not of the form "X ~> collection<Y>" as stated above, then this method simply
      /// returns the given "e".
      ///
      /// Dafny does not have a UNION comprehension, so the expression returned has the form
      ///
      ///     { obj: Y | exists x: X :: obj in e(x) }
      ///
      /// which in Dafny notation is written
      ///
      ///     set x: X, obj: Y | obj in e(x) :: obj
      ///
      /// Note, since Y is a reference type and there is, at any one time, only a finite number of references,
      /// the result type is finite.
      ///
      /// Note: A pending improvement would be to limit the range of the set comprehension to the values for x
      /// that satisfy e's precondition.
      /// </summary>
      public static Expression FrameArrowToObjectSet(Expression e) {
        Contract.Requires(e != null);
        var arrowType = e.Type.AsArrowType;
        if (arrowType == null) {
          return e;
        }
        var collectionType = arrowType.Result.NormalizeToAncestorType().AsCollectionType;
        if (collectionType == null || collectionType is MapType) {
          return e;
        }
        var elementType = collectionType.Arg; // "elementType" is called "Y" in the description of this method, above
        if (!elementType.IsRefType) {
          return e;
        }

        var boundVarDecls = new List<BoundVar>();
        var boundVarUses = new List<Expression>();
        var i = 0;
        foreach (var functionArgumentType in arrowType.Args) {
          var bv = new BoundVar(e.Origin, $"_x{i}", functionArgumentType);
          boundVarDecls.Add(bv);
          boundVarUses.Add(new IdentifierExpr(e.Origin, bv.Name) { Type = bv.Type, Var = bv });
          i++;
        }
        var objVar = new BoundVar(e.Origin, "_obj", elementType.NormalizeExpand());
        var objUse = new IdentifierExpr(e.Origin, objVar.Name) { Type = objVar.Type, Var = objVar };
        boundVarDecls.Add(objVar);

        var collection = new ApplyExpr(e.Origin, e, boundVarUses, Token.NoToken) {
          Type = collectionType
        };
        var resolvedOpcode = collectionType.ResolvedOpcodeForIn;

        var inCollection = new BinaryExpr(e.Origin, BinaryExpr.Opcode.In, objUse, collection) {
          ResolvedOp = resolvedOpcode,
          Type = Type.Bool
        };

        var attributes = new Attributes("_reads", [], null);
        return new SetComprehension(e.Origin, true, boundVarDecls, inCollection, objUse, attributes) {
          Type = new SetType(true, elementType)
        };
      }

      protected override void VisitExpression(Expression expr, BoundsDiscoveryContext context) {
        if (expr is LambdaExpr lambdaExpr) {
          lambdaExpr.Reads.Expressions.ForEach(DesugarFunctionsInFrameClause);

          // Make the context more specific when visiting inside a lambda expression
          context = new BoundsDiscoveryContext(context, lambdaExpr);
        }
        base.VisitExpression(expr, context);
      }

      protected override bool VisitOneExpression(Expression expr, BoundsDiscoveryContext context) {
        if (expr is ComprehensionExpr and not LambdaExpr) {
          var e = (ComprehensionExpr)expr;
          // apply bounds discovery to quantifiers, finite sets, and finite maps
          Expression whereToLookForBounds = null;
          var polarity = true;
          if (e is QuantifierExpr quantifierExpr) {
            whereToLookForBounds = quantifierExpr.LogicalBody();
            polarity = quantifierExpr is ExistsExpr;
          } else if (e is SetComprehension setComprehension) {
            whereToLookForBounds = setComprehension.Range;
          } else if (e is MapComprehension) {
            whereToLookForBounds = e.Range;
          } else {
            Contract.Assert(false);  // otherwise, unexpected ComprehensionExpr
          }
          if (whereToLookForBounds != null) {
            e.Bounds = DiscoverBestBounds_MultipleVars_AllowReordering(e.BoundVars, whereToLookForBounds, polarity);
            if (!context.AllowedToDependOnAllocationState) {
              foreach (var bv in BoundedPool.MissingBounds(e.BoundVars, e.Bounds,
                         BoundedPool.PoolVirtues.IndependentOfAlloc)) {
                var how = Attributes.Contains(e.Attributes, "_reads") ? "(implicitly by using a function in a reads clause) " : "";
                var message =
                  $"a {e.WhatKind} involved in a {context.Kind} {how}is not allowed to depend on the set of allocated references," +
                  $" but values of '{bv.Name}' (of type '{bv.Type}') may contain references";
                if (bv.Type.IsTypeParameter || bv.Type.IsAbstractType) {
                  message += $" (perhaps declare its type as '{bv.Type}(!new)')";
                }
                message += " (see documentation for 'older' parameters)";
                Reporter.Error(MessageSource.Resolver, e, message);
              }
            }

            if ((e as SetComprehension)?.Finite == true || (e as MapComprehension)?.Finite == true) {
              // the comprehension had better produce a finite set
              if (e.Type.HasFinitePossibleValues) {
                // This means the set is finite, regardless of if the Range is bounded.  So, we don't give any error here.
                // However, if this expression is used in a non-ghost context (which is not yet known at this stage of
                // resolution), the resolver will generate an error about that later.
              } else {
                // we cannot be sure that the set/map really is finite
                foreach (var bv in BoundedPool.MissingBounds(e.BoundVars, e.Bounds,
                           BoundedPool.PoolVirtues.Finite)) {
                  Reporter.Error(MessageSource.Resolver, e,
                    "the result of a {0} must be finite, but Dafny's heuristics can't figure out how to produce a bounded set of values for '{1}'",
                    e.WhatKind, bv.Name);
                }
              }
            }
          }

        }

        return base.VisitOneExpression(expr, context);
      }
    }

    /// <summary>
    /// For a list of variables "bvars", returns a list of best bounds for each respective variable.
    /// If no bound is found for a variable "v", then the bound for "v" in the returned list is set to "null".
    /// </summary>
    public static List<BoundedPool> DiscoverBestBounds_MultipleVars<VT>(List<VT> bvars, Expression expr,
      bool polarity) where VT : IVariable {
      Contract.Requires(bvars != null);
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<List<BoundedPool>>() != null);
      foreach (var bv in bvars) {
        var c = GetImpliedTypeConstraint(bv, bv.Type);
        expr = polarity ? Expression.CreateAnd(c, expr, false) : Expression.CreateImplies(c, expr, false);
      }
      var bests = DiscoverAllBounds_Aux_MultipleVars(bvars, expr, polarity);
      return bests;
    }

    public static List<BoundedPool> DiscoverBestBounds_MultipleVars_AllowReordering<VT>(List<VT> bvars, Expression expr,
      bool polarity) where VT : IVariable {
      Contract.Requires(bvars != null);
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<List<BoundedPool>>() != null);
      var bounds = DiscoverBestBounds_MultipleVars(bvars, expr, polarity);
      if (bvars.Count > 1) {
        // It may be helpful to try all permutations (or, better yet, to use an algorithm that keeps track of the dependencies
        // and discovers good bounds more efficiently). However, all permutations would be expensive. Therefore, we try just one
        // other permutation, namely the reversal "bvars". This covers the important case where there are two bound variables
        // that work out in the opposite order. It also covers one more case for the (probably rare) case of there being more
        // than two bound variables.
        var bvarsMissyElliott = new List<VT>(bvars);  // make a copy
        bvarsMissyElliott.Reverse();  // and then flip it and reverse it, Ti esrever dna ti pilf nwod gnaht ym tup I
        var boundsMissyElliott = DiscoverBestBounds_MultipleVars(bvarsMissyElliott, expr, polarity);
        // Figure out which one seems best
        var meBetter = 0;
        for (int i = 0; i < bvars.Count; i++) {
          var orig = bounds[i];
          var me = boundsMissyElliott[i];
          if (orig == null && me != null) {
            meBetter = 1; break; // end game
          } else if (orig != null && me == null) {
            meBetter = -1; break; // end game
          } else if (orig != null && me != null) {
            if ((orig.Virtues & BoundedPool.PoolVirtues.Finite) != 0) { meBetter--; }
            if ((orig.Virtues & BoundedPool.PoolVirtues.Enumerable) != 0) { meBetter--; }
            if ((me.Virtues & BoundedPool.PoolVirtues.Finite) != 0) { meBetter++; }
            if ((me.Virtues & BoundedPool.PoolVirtues.Enumerable) != 0) { meBetter++; }
          }
        }
        if (meBetter > 0) {
          // yes, this reordering seems to have been better
          bvars.Reverse();
          return boundsMissyElliott;
        }
      }
      return bounds;
    }

    private static List<BoundedPool> DiscoverAllBounds_Aux_MultipleVars<VT>(List<VT> bvars, Expression expr,
      bool polarity) where VT : IVariable {
      Contract.Requires(bvars != null);
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<List<BoundedPool>>() != null);
      Contract.Ensures(Contract.Result<List<BoundedPool>>().Count == bvars.Count);
      var knownBounds = new List<BoundedPool>();
      for (var j = 0; j < bvars.Count; j++) {
        knownBounds.Add(null);
      }
      // Note, in the following loop, it's important to go backwards, because DiscoverAllBounds_Aux_SingleVar assumes "knownBounds" has been
      // filled in for higher-indexed variables.
      for (var j = bvars.Count; 0 <= --j;) {
        var bounds = DiscoverAllBounds_Aux_SingleVar(bvars, j, expr, polarity, knownBounds, out _);
        knownBounds[j] = BoundedPool.GetBest(bounds);
#if DEBUG_PRINT
        if (knownBounds[j] is IntBoundedPool) {
          var ib = (IntBoundedPool)knownBounds[j];
          var lo = ib.LowerBound == null ? "" : Printer.ExprToString(ib.LowerBound);
          var hi = ib.UpperBound == null ? "" : Printer.ExprToString(ib.UpperBound);
          Console.WriteLine("DEBUG: Bound for var {3}, {0}:  {1} .. {2}", bvars[j].Name, lo, hi, j);
        } else if (knownBounds[j] is SetBoundedPool) {
          Console.WriteLine("DEBUG: Bound for var {2}, {0}:  in {1}", bvars[j].Name, Printer.ExprToString(((SetBoundedPool)knownBounds[j]).Set), j);
        } else {
          Console.WriteLine("DEBUG: Bound for var {2}, {0}:  {1}", bvars[j].Name, knownBounds[j], j);
        }
#endif
      }
      return knownBounds;
    }

    public static List<BoundedPool> DiscoverAllBounds_SingleVar<VT>(VT v, Expression expr,
      out bool constraintConsistsSolelyOfRangeConstraints) where VT : IVariable {
      expr = Expression.CreateAnd(GetImpliedTypeConstraint(v, v.Type), expr);
      return DiscoverAllBounds_Aux_SingleVar([v], 0, expr, true,
        [null], out constraintConsistsSolelyOfRangeConstraints);
    }

    /// <summary>
    /// Returns a list of (possibly partial) bounds for "bvars[j]", each of which can be written without mentioning any variable in "bvars[j..]"
    /// that is not bounded.
    /// </summary>
    private static List<BoundedPool> DiscoverAllBounds_Aux_SingleVar<VT>(List<VT> bvars, int j, Expression expr,
      bool polarity, List<BoundedPool> knownBounds, out bool constraintConsistsSolelyOfRangeConstraints) where VT : IVariable {
      Contract.Requires(bvars != null);
      Contract.Requires(0 <= j && j < bvars.Count);
      Contract.Requires(expr != null);
      Contract.Requires(knownBounds != null);
      Contract.Requires(knownBounds.Count == bvars.Count);
      var bv = bvars[j];
      var bvType = bv.Type.NormalizeToAncestorType();
      var bounds = new List<BoundedPool>();

      // Maybe the type itself gives a bound
      if (bvType.IsBoolType) {
        bounds.Add(new BoolBoundedPool());
      } else if (bvType.IsCharType) {
        bounds.Add(new CharBoundedPool());
      } else if (bvType.IsDatatype && bvType.AsDatatype.HasFinitePossibleValues) {
        bounds.Add(new DatatypeBoundedPool(bvType.AsDatatype));
      } else if (bvType.IsNumericBased(Type.NumericPersuasion.Int)) {
        bounds.Add(new AssignSuchThatStmt.WiggleWaggleBound());
      } else if (!bvType.MayInvolveReferences) {
        // in the next line, use bv.Type, even though we compared with bvType
        bounds.Add(new AllocFreeBoundedPool(bv.Type));
      }

      // Go through the conjuncts of the range expression to look for bounds.
      // Only very specific conjuncts qualify for "constraintConsistsSolelyOfRangeConstraints". To make the bookkeeping
      // of these simple, we count the total number of conjuncts and the number of qualifying conjuncts. Then, after the
      // loop, we can compare these.
      var totalNumberOfConjuncts = 0;
      var conjunctsQualifyingAsRangeConstraints = 0;
      foreach (var conjunct in NormalizedConjuncts(expr, polarity)) {
        totalNumberOfConjuncts++;

        if (conjunct is IdentifierExpr) {
          var ide = (IdentifierExpr)conjunct;
          if (ide.Var == (IVariable)bv) {
            Contract.Assert(bvType.IsBoolType);
            bounds.Add(new ExactBoundedPool(Expression.CreateBoolLiteral(Token.NoToken, true)));
          }
          continue;
        }
        if (conjunct is UnaryOpExpr or OldExpr) {
          // we also consider a unary expression sitting immediately inside an old
          var unary = conjunct as UnaryOpExpr ?? ((OldExpr)conjunct).Expr.Resolved as UnaryOpExpr;
          if (unary != null) {
            if (unary.E.Resolved is IdentifierExpr ide && ide.Var == (IVariable)bv) {
              if (unary.ResolvedOp == UnaryOpExpr.ResolvedOpcode.BoolNot) {
                bounds.Add(new ExactBoundedPool(Expression.CreateBoolLiteral(Token.NoToken, false)));
              } else if (unary.ResolvedOp == UnaryOpExpr.ResolvedOpcode.Allocated) {
                bounds.Add(new ExplicitAllocatedBoundedPool());
              }
            }
          }
          continue;
        }
        if (conjunct is FunctionCallExpr functionCallExpr) {
          DiscoverBoundsFunctionCallExpr(functionCallExpr, bv, bounds);
          continue;
        }
        var c = conjunct as BinaryExpr;
        if (c == null) {
          // other than what we already covered above, we only know what to do with binary expressions
          continue;
        }
        var e0 = c.E0;
        var e1 = c.E1;
        int whereIsBv = SanitizeForBoundDiscovery(bvars, j, c.ResolvedOp, knownBounds, ref e0, ref e1);
        if (whereIsBv < 0) {
          continue;
        }
        switch (c.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.InSet:
            if (whereIsBv == 0) {
              var setType = e1.Type.NormalizeToAncestorType().AsSetType;
              bounds.Add(new SetBoundedPool(e1, e0.Type, setType.Arg, setType.Finite));
            }
            break;
          case BinaryExpr.ResolvedOpcode.Subset:
            if (whereIsBv == 0) {
              var setType = e1.Type.NormalizeToAncestorType().AsSetType;
              bounds.Add(new SubSetBoundedPool(e1, setType.Finite));
            } else {
              bounds.Add(new SuperSetBoundedPool(e0));
            }
            break;
          case BinaryExpr.ResolvedOpcode.InMultiSet:
            if (whereIsBv == 0) {
              bounds.Add(new MultiSetBoundedPool(e1, e0.Type, e1.Type.NormalizeToAncestorType().AsMultiSetType.Arg));
            }
            break;
          case BinaryExpr.ResolvedOpcode.InSeq:
            if (whereIsBv == 0 && e1.Type.NormalizeToAncestorType().AsSeqType is { } seqType) {
              bounds.Add(new SeqBoundedPool(e1, e0.Type, seqType.Arg));
            }
            break;
          case BinaryExpr.ResolvedOpcode.InMap:
            if (whereIsBv == 0) {
              var mapType = e1.Type.NormalizeToAncestorType().AsMapType;
              bounds.Add(new MapBoundedPool(e1, e0.Type, mapType.Arg, mapType.Finite));
            }
            break;
          case BinaryExpr.ResolvedOpcode.EqCommon:
          case BinaryExpr.ResolvedOpcode.SetEq:
          case BinaryExpr.ResolvedOpcode.SeqEq:
          case BinaryExpr.ResolvedOpcode.MultiSetEq:
          case BinaryExpr.ResolvedOpcode.MapEq:
            conjunctsQualifyingAsRangeConstraints++;
            var otherOperand = whereIsBv == 0 ? e1 : e0;
            bounds.Add(new ExactBoundedPool(otherOperand));
            break;
          case BinaryExpr.ResolvedOpcode.Gt:
          case BinaryExpr.ResolvedOpcode.Ge:
            Contract.Assert(false);
            throw new Cce.UnreachableException(); // promised by postconditions of NormalizedConjunct
          case BinaryExpr.ResolvedOpcode.Lt:
            if (e0.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
              conjunctsQualifyingAsRangeConstraints++;
              if (whereIsBv == 0) {
                // bv < E
                bounds.Add(new IntBoundedPool(null, e1));
              } else {
                // E < bv
                bounds.Add(new IntBoundedPool(Expression.CreateIncrement(e0, 1), null));
              }
            }
            break;
          case BinaryExpr.ResolvedOpcode.Le:
            conjunctsQualifyingAsRangeConstraints++;
            if (e0.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
              if (whereIsBv == 0) {
                // bv <= E
                bounds.Add(new IntBoundedPool(null, Expression.CreateIncrement(e1, 1)));
              } else {
                // E <= bv
                bounds.Add(new IntBoundedPool(e0, null));
              }
            }
            break;
          case BinaryExpr.ResolvedOpcode.RankLt:
            if (whereIsBv == 0) {
              bounds.Add(new DatatypeInclusionBoundedPool(e0.Type.IsIndDatatype));
            }
            break;
          case BinaryExpr.ResolvedOpcode.RankGt:
            if (whereIsBv == 1) {
              bounds.Add(new DatatypeInclusionBoundedPool(e1.Type.IsIndDatatype));
            }
            break;
          default:
            break;
        }
      }
      constraintConsistsSolelyOfRangeConstraints = conjunctsQualifyingAsRangeConstraints == totalNumberOfConjuncts;
      return bounds;
    }

    private static void DiscoverBoundsFunctionCallExpr<VT>(FunctionCallExpr fce, VT boundVariable, List<BoundedPool> bounds)
      where VT : IVariable {
      Contract.Requires(fce != null);
      Contract.Requires(boundVariable != null);
      Contract.Requires(bounds != null);

      var formals = fce.Function.Ins;
      Contract.Assert(formals.Count == fce.Args.Count);
      if (Enumerable.Zip(formals, fce.Args).Any(t => t.Item1.IsOlder && t.Item2.Resolved is IdentifierExpr ide && ide.Var == (IVariable)boundVariable)) {
        bounds.Add(new OlderBoundedPool());
        return;
      }
    }

    /// <summary>
    /// Returns all conjuncts of "expr" in "polarity" positions.  That is, if "polarity" is "true", then
    /// returns the conjuncts of "expr" in positive positions; else, returns the conjuncts of "expr" in
    /// negative positions.  The method considers a canonical-like form of the expression that pushes
    /// negations inwards far enough that one can determine what the result is going to be (so, almost
    /// a negation normal form).
    /// As a convenience, arithmetic inequalities are rewritten so that the negation of an arithmetic
    /// inequality is never returned and the comparisons > and >= are never returned; the negation of
    /// a common equality or disequality is rewritten analogously.
    /// Requires "expr" to be successfully resolved.
    /// Ensures that what is returned is not a ConcreteSyntaxExpression.
    /// </summary>
    static IEnumerable<Expression> NormalizedConjuncts(Expression expr, bool polarity) {
      // We consider 5 cases.  To describe them, define P(e)=Conjuncts(e,true) and N(e)=Conjuncts(e,false).
      //   *  X ==> Y    is treated as a shorthand for !X || Y, and so is described by the remaining cases
      //   *  X && Y     P(_) = P(X),P(Y)    and    N(_) = !(X && Y)
      //   *  X || Y     P(_) = (X || Y)     and    N(_) = N(X),N(Y)
      //   *  !X         P(_) = N(X)         and    N(_) = P(X)
      //   *  else       P(_) = else         and    N(_) = !else
      // So for ==>, we have:
      //   *  X ==> Y    P(_) = P(!X || Y) = (!X || Y) = (X ==> Y)
      //                 N(_) = N(!X || Y) = N(!X),N(Y) = P(X),N(Y)
      expr = expr.Resolved;

      // Binary expressions
      var b = expr as BinaryExpr;
      if (b != null) {
        bool breakDownFurther = false;
        bool p0 = polarity;
        switch (b.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.And:
            breakDownFurther = polarity;
            break;
          case BinaryExpr.ResolvedOpcode.Or:
            breakDownFurther = !polarity;
            break;
          case BinaryExpr.ResolvedOpcode.Imp:
            breakDownFurther = !polarity;
            p0 = !p0;
            break;
          default:
            break;
        }
        if (breakDownFurther) {
          foreach (var c in NormalizedConjuncts(b.E0, p0)) {
            yield return c;
          }
          foreach (var c in NormalizedConjuncts(b.E1, polarity)) {
            yield return c;
          }
          yield break;
        }
      }

      // Unary expression
      var u = expr as UnaryOpExpr;
      if (u != null && u.Op == UnaryOpExpr.Opcode.Not) {
        foreach (var c in NormalizedConjuncts(u.E, !polarity)) {
          yield return c;
        }
        yield break;
      }

      // no other case applied, so return the expression or its negation, but first clean it up a little
      b = expr as BinaryExpr;
      if (b != null) {
        BinaryExpr.Opcode newOp;
        BinaryExpr.ResolvedOpcode newROp;
        bool swapOperands;
        switch (b.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.Gt:  // A > B         yield polarity ? (B < A) : (A <= B);
            newOp = polarity ? BinaryExpr.Opcode.Lt : BinaryExpr.Opcode.Le;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.Lt : BinaryExpr.ResolvedOpcode.Le;
            swapOperands = polarity;
            break;
          case BinaryExpr.ResolvedOpcode.Ge:  // A >= B        yield polarity ? (B <= A) : (A < B);
            newOp = polarity ? BinaryExpr.Opcode.Le : BinaryExpr.Opcode.Lt;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.Le : BinaryExpr.ResolvedOpcode.Lt;
            swapOperands = polarity;
            break;
          case BinaryExpr.ResolvedOpcode.Le:  // A <= B        yield polarity ? (A <= B) : (B < A);
            newOp = polarity ? BinaryExpr.Opcode.Le : BinaryExpr.Opcode.Lt;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.Le : BinaryExpr.ResolvedOpcode.Lt;
            swapOperands = !polarity;
            break;
          case BinaryExpr.ResolvedOpcode.Lt:  // A < B         yield polarity ? (A < B) : (B <= A);
            newOp = polarity ? BinaryExpr.Opcode.Lt : BinaryExpr.Opcode.Le;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.Lt : BinaryExpr.ResolvedOpcode.Le;
            swapOperands = !polarity;
            break;
          case BinaryExpr.ResolvedOpcode.EqCommon:  // A == B         yield polarity ? (A == B) : (A != B);
            newOp = polarity ? BinaryExpr.Opcode.Eq : BinaryExpr.Opcode.Neq;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.EqCommon : BinaryExpr.ResolvedOpcode.NeqCommon;
            swapOperands = false;
            break;
          case BinaryExpr.ResolvedOpcode.NeqCommon:  // A != B         yield polarity ? (A != B) : (A == B);
            newOp = polarity ? BinaryExpr.Opcode.Neq : BinaryExpr.Opcode.Eq;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.NeqCommon : BinaryExpr.ResolvedOpcode.EqCommon;
            swapOperands = false;
            break;
          case BinaryExpr.ResolvedOpcode.NotInSet:  // A !in B         yield polarity ? (A !in B) : (A in B);
            newOp = polarity ? BinaryExpr.Opcode.NotIn : BinaryExpr.Opcode.In;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.NotInSet : BinaryExpr.ResolvedOpcode.InSet;
            swapOperands = false;
            break;
          case BinaryExpr.ResolvedOpcode.NotInSeq:  // A !in B         yield polarity ? (A !in B) : (A in B);
            newOp = polarity ? BinaryExpr.Opcode.NotIn : BinaryExpr.Opcode.In;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.NotInSeq : BinaryExpr.ResolvedOpcode.InSeq;
            swapOperands = false;
            break;
          case BinaryExpr.ResolvedOpcode.NotInMultiSet:  // A !in B         yield polarity ? (A !in B) : (A in B);
            newOp = polarity ? BinaryExpr.Opcode.NotIn : BinaryExpr.Opcode.In;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.NotInMultiSet : BinaryExpr.ResolvedOpcode.InMultiSet;
            swapOperands = false;
            break;
          case BinaryExpr.ResolvedOpcode.NotInMap:  // A !in B         yield polarity ? (A !in B) : (A in B);
            newOp = polarity ? BinaryExpr.Opcode.NotIn : BinaryExpr.Opcode.In;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.NotInMap : BinaryExpr.ResolvedOpcode.InMap;
            swapOperands = false;
            break;
          default:
            goto JUST_RETURN_IT;
        }
        if (newROp != b.ResolvedOp || swapOperands) {
          b = new BinaryExpr(b.Origin, newOp, swapOperands ? b.E1 : b.E0, swapOperands ? b.E0 : b.E1);
          b.ResolvedOp = newROp;
          b.Type = Type.Bool;
          yield return b;
          yield break;
        }
      }
    JUST_RETURN_IT:;
      if (polarity) {
        yield return expr;
      } else {
        expr = new UnaryOpExpr(expr.Origin, UnaryOpExpr.Opcode.Not, expr);
        expr.Type = Type.Bool;
        yield return expr;
      }
    }

    /// <summary>
    /// If the return value is negative, the resulting "e0" and "e1" should not be used.
    /// Otherwise, the following is true on return:
    /// The new "e0 op e1" is equivalent to the old "e0 op e1".
    /// One of "e0" and "e1" is the identifier "boundVars[bvi]"; the return value is either 0 or 1, and indicates which.
    /// The other of "e0" and "e1" is an expression whose free variables are not among "boundVars[bvi..]".
    /// Ensures that the resulting "e0" and "e1" are not ConcreteSyntaxExpression's.
    /// </summary>
    static int SanitizeForBoundDiscovery<VT>(List<VT> boundVars, int bvi, BinaryExpr.ResolvedOpcode op,
      List<BoundedPool> knownBounds,
      ref Expression e0, ref Expression e1) where VT : IVariable {
      Contract.Requires(boundVars != null);
      Contract.Requires(0 <= bvi && bvi < boundVars.Count);
      Contract.Requires(knownBounds != null);
      Contract.Requires(knownBounds.Count == boundVars.Count);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<int>() < 2);
      Contract.Ensures(!(Contract.ValueAtReturn(out e0) is ConcreteSyntaxExpression));
      Contract.Ensures(!(Contract.ValueAtReturn(out e1) is ConcreteSyntaxExpression));

      IVariable bv = boundVars[bvi];
      e0 = e0.Resolved;
      e1 = e1.Resolved;

      // make an initial assessment of where bv is; to continue, we need bv to appear in exactly one operand
      var fv0 = FreeVariables(e0);
      var fv1 = FreeVariables(e1);
      Expression thisSide;
      Expression thatSide;
      int whereIsBv;
      if (fv0.Contains(bv)) {
        if (fv1.Contains(bv)) {
          return -1;
        }
        whereIsBv = 0;
        thisSide = e0;
        thatSide = e1;
      } else if (fv1.Contains(bv)) {
        whereIsBv = 1;
        thisSide = e1;
        thatSide = e0;
      } else {
        return -1;
      }

      // Next, clean up the side where bv is by adjusting both sides of the expression
      switch (op) {
        case BinaryExpr.ResolvedOpcode.EqCommon:
        case BinaryExpr.ResolvedOpcode.NeqCommon:
        case BinaryExpr.ResolvedOpcode.Gt:
        case BinaryExpr.ResolvedOpcode.Ge:
        case BinaryExpr.ResolvedOpcode.Le:
        case BinaryExpr.ResolvedOpcode.Lt:
          // Repeatedly move additive or subtractive terms from thisSide to thatSide
          while (true) {
            var bin = thisSide as BinaryExpr;
            if (bin == null) {
              if (thisSide is ConversionExpr conversionExpr &&
                  thisSide.Type.NormalizeExpand().Equals(conversionExpr.E.Type.NormalizeExpand())) {
                thisSide = conversionExpr.E.Resolved;
              } else {
                break; // done simplifying
              }

            } else if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Add) {
              // Change "A+B op C" into either "A op C-B" or "B op C-A", depending on where we find bv among A and B.
              if (!FreeVariables(bin.E1).Contains(bv)) {
                thisSide = bin.E0.Resolved;
                thatSide = new BinaryExpr(bin.Origin, BinaryExpr.Opcode.Sub, thatSide, bin.E1);
              } else if (!FreeVariables(bin.E0).Contains(bv)) {
                thisSide = bin.E1.Resolved;
                thatSide = new BinaryExpr(bin.Origin, BinaryExpr.Opcode.Sub, thatSide, bin.E0);
              } else {
                break; // done simplifying
              }
              ((BinaryExpr)thatSide).ResolvedOp = BinaryExpr.ResolvedOpcode.Sub;
              thatSide.Type = bin.Type;

            } else if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Sub) {
              // Change "A-B op C" in a similar way.
              if (!FreeVariables(bin.E1).Contains(bv)) {
                // change to "A op C+B"
                thisSide = bin.E0.Resolved;
                thatSide = new BinaryExpr(bin.Origin, BinaryExpr.Opcode.Add, thatSide, bin.E1);
                ((BinaryExpr)thatSide).ResolvedOp = BinaryExpr.ResolvedOpcode.Add;
              } else if (!FreeVariables(bin.E0).Contains(bv)) {
                // In principle, change to "-B op C-A" and then to "B dualOp A-C".  But since we don't want
                // to change "op", we instead end with "A-C op B" and switch the mapping of thisSide/thatSide
                // to e0/e1 (by inverting "whereIsBv").
                thisSide = bin.E1.Resolved;
                thatSide = new BinaryExpr(bin.Origin, BinaryExpr.Opcode.Sub, bin.E0, thatSide);
                ((BinaryExpr)thatSide).ResolvedOp = BinaryExpr.ResolvedOpcode.Sub;
                whereIsBv = 1 - whereIsBv;
              } else {
                break; // done simplifying
              }
              thatSide.Type = bin.Type;

            } else {
              break; // done simplifying
            }
          }
          break;

        default:
          break;
      }
      // our transformation above maintained the following invariant:
      Contract.Assert(!FreeVariables(thatSide).Contains(bv));

      // Now, see if the interesting side is simply bv itself
      if (Expression.StripParensAndCasts(thisSide) is IdentifierExpr { Var: var thisSideVar } && thisSideVar == bv) {
        // we're cool
      } else {
        // no, the situation is more complicated than we care to understand
        return -1;
      }

      // Finally, check the bound variables of "thatSide". We allow "thatSide" to
      // depend on bound variables that are listed before "bv" (that is, a bound variable
      // "boundVars[k]" where "k < bvi"). By construction, "thatSide" does not depend
      // on "bv". Generally, for any bound variable "bj" that is listed after "bv"
      // (that is, "bj" is some "boundVars[j]" where "bvi < j"), we do not allow
      // "thatSide" to depend on "bv", but there is an important exception:
      // If
      //   *  "op" makes "thatSide" denote an integer upper bound on "bv" (or, analogously,
      //      a integer lower bound),
      //   *  "thatSide" depends on "bj",
      //   *  "thatSide" is monotonic in "bj",
      //   *  "bj" has a known integer upper bound "u",
      //   *  "u" does not depend on "bv" or any bound variable listed after "bv"
      //      (from the way we're constructing bounds, we already know that "u"
      //      does not depend on "bj" or any bound variable listed after "bj")
      // then we can substitute "u" for "bj" in "thatSide".
      // By going from right to left, we can make the rule above slightly more
      // liberal by considering a cascade of substitutions.
      var fvThatSide = FreeVariables(thatSide);
      for (int j = boundVars.Count; bvi + 1 <= --j;) {
        if (fvThatSide.Contains(boundVars[j])) {
          if (knownBounds[j] is IntBoundedPool jBounds) {
            Expression u = null;
            if (op is BinaryExpr.ResolvedOpcode.Lt or BinaryExpr.ResolvedOpcode.Le) {
              u = whereIsBv == 0 ? jBounds.UpperBound : jBounds.LowerBound;
            } else if (op == BinaryExpr.ResolvedOpcode.Gt || op == BinaryExpr.ResolvedOpcode.Ge) {
              u = whereIsBv == 0 ? jBounds.LowerBound : jBounds.UpperBound;
            }
            if (u != null && !FreeVariables(u).Contains(bv) && IsMonotonic(u, boundVars[j], true)) {
              thatSide = BoogieGenerator.Substitute(thatSide, boundVars[j], u);
              fvThatSide = FreeVariables(thatSide);
              continue;
            }
          }
          return -1; // forget about "bv OP thatSide"
        }
      }

      // As we return, also return the adjusted sides
      if (whereIsBv == 0) {
        e0 = thisSide;
        e1 = thatSide;
      } else {
        e0 = thatSide;
        e1 = thisSide;
      }
      return whereIsBv;
    }

    /// <summary>
    /// If "position", then returns "true" if "x" occurs only positively in "expr".
    /// If "!position", then returns "true" if "x" occurs only negatively in "expr".
    /// </summary>
    public static bool IsMonotonic(Expression expr, IVariable x, bool position) {
      Contract.Requires(expr != null && expr.Type != null);
      Contract.Requires(x != null);

      if (expr is IdentifierExpr identifierExpr) {
        return identifierExpr.Var != x || position;
      } else if (expr is BinaryExpr binaryExpr) {
        if (binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Add) {
          return IsMonotonic(binaryExpr.E0, x, position) && IsMonotonic(binaryExpr.E1, x, position);
        } else if (binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Sub) {
          return IsMonotonic(binaryExpr.E0, x, position) && IsMonotonic(binaryExpr.E1, x, !position);
        }
      }
      return !FreeVariables(expr).Contains(x);
    }
  }
}
