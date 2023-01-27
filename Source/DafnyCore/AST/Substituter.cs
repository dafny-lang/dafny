using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie.Clustering;

namespace Microsoft.Dafny {
  /// <summary>
  /// The substituter has methods to create an expression from an existing one, where the new one has the indicated
  /// substitutions for "this" (receiverReplacement), variables (substMap), and types (typeMap).
  /// CAUTION:  The result of the substitution is intended for use by TrExpr, not for well-formedness checks.  In
  /// particular, the substituter does not copy parts of an expression that are used only for well-formedness checks.
  /// </summary>
  public class Substituter {
    protected readonly Expression receiverReplacement;
    protected readonly Dictionary<IVariable, Expression> substMap;
    protected readonly Dictionary<TypeParameter, Type> typeMap;
    protected readonly Label oldHeapLabel;

    public static readonly Substituter EMPTY = new Substituter(null, new Dictionary<IVariable, Expression>(), new Dictionary<TypeParameter, Type>());

    public Substituter(Expression receiverReplacement, Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, Type> typeMap, Label oldHeapLabel = null) {
      Contract.Requires(substMap != null);
      Contract.Requires(typeMap != null);
      this.receiverReplacement = receiverReplacement;
      this.substMap = substMap;
      this.typeMap = typeMap;
      this.oldHeapLabel = oldHeapLabel;
    }
    public virtual Expression Substitute(Expression expr) {
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<Expression>() != null);

      Expression newExpr = null;  // set to non-null value only if substitution has any effect; if non-null, the .Type of newExpr will be filled in at end

      if (expr is StaticReceiverExpr) {
        var e = (StaticReceiverExpr)expr;
        var ty = e.Type.Subst(typeMap);
        return new StaticReceiverExpr(e.RangeToken, ty, e.IsImplicit) { Type = ty };
      } else if (expr is LiteralExpr literalExpr) {
        if (literalExpr.Value == null) {
          var ty = literalExpr.Type.Subst(typeMap);
          if (ty != literalExpr.Type) {
            return new LiteralExpr(literalExpr.RangeToken) { Type = ty };
          }
        } else {
          // nothing to substitute
        }
      } else if (expr is Translator.BoogieWrapper) {
        var e = (Translator.BoogieWrapper)expr;
        var ty = e.Type.Subst(typeMap);
        if (ty != e.Type) {
          return new Translator.BoogieWrapper(e.Expr, ty);
        }
      } else if (expr is WildcardExpr) {
        // nothing to substitute
      } else if (expr is ThisExpr) {
        if (receiverReplacement == null) {
          return expr;
        } else {
          return new ParensExpression(expr.RangeToken, receiverReplacement) {
            ResolvedExpression = receiverReplacement,
            RangeToken = expr.RangeToken,
            Type = receiverReplacement.Type
          };
        }
      } else if (expr is IdentifierExpr) {
        IdentifierExpr e = (IdentifierExpr)expr;
        Expression substExpr;
        if (substMap.TryGetValue(e.Var, out substExpr)) {
          var substIdExpr = substExpr as IdentifierExpr;
          Expression substExprFinal;
          if (substIdExpr != null) {
            // clone it, using the source location of the original
            substExprFinal = new IdentifierExpr(expr.RangeToken, substIdExpr.Var);
          } else {
            if (substExpr.RangeToken != e.RangeToken) {
              var substExprParens = new ParensExpression(expr.RangeToken, substExpr);
              substExprParens.Type = substExpr.Type;
              substExprParens.ResolvedExpression = substExpr;
              substExprFinal = substExprParens;
            } else {
              substExprFinal = substExpr;
            }
          }

          return cce.NonNull(substExprFinal);
        }
      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        List<Expression> newElements = SubstituteExprList(e.Elements);
        if (newElements != e.Elements || e.Type.Subst(typeMap) != e.Type) {
          if (expr is SetDisplayExpr) {
            newExpr = new SetDisplayExpr(expr.RangeToken, ((SetDisplayExpr)expr).Finite, newElements);
          } else if (expr is MultiSetDisplayExpr) {
            newExpr = new MultiSetDisplayExpr(expr.RangeToken, newElements);
          } else {
            newExpr = new SeqDisplayExpr(expr.RangeToken, newElements);
          }
        }
      } else if (expr is MapDisplayExpr) {
        var e = (MapDisplayExpr)expr;
        var elmts = new List<ExpressionPair>();
        var anyChanges = false;
        foreach (var ep in e.Elements) {
          var a = Substitute(ep.A);
          var b = Substitute(ep.B);
          elmts.Add(new ExpressionPair(a, b));
          if (a != ep.A || b != ep.B) {
            anyChanges = true;
          }
        }
        var ty = e.Type.Subst(typeMap);
        if (anyChanges || ty != e.Type) {
          newExpr = new MapDisplayExpr(expr.RangeToken, e.Finite, elmts);
        }
      } else if (expr is MemberSelectExpr) {
        var mse = (MemberSelectExpr)expr;
        var newObj = Substitute(mse.Obj);
        var newTypeApplicationAtEnclosingClass = SubstituteTypeList(mse.TypeApplication_AtEnclosingClass);
        var newTypeApplicationJustMember = SubstituteTypeList(mse.TypeApplication_JustMember);
        if (newObj != mse.Obj ||
            newTypeApplicationAtEnclosingClass != mse.TypeApplication_AtEnclosingClass ||
            newTypeApplicationJustMember != mse.TypeApplication_JustMember) {
          var fseNew = new MemberSelectExpr(mse.RangeToken, newObj, mse.MemberName) {
            Member = mse.Member,
            TypeApplication_AtEnclosingClass = newTypeApplicationAtEnclosingClass,
            TypeApplication_JustMember = newTypeApplicationJustMember,
            AtLabel = mse.AtLabel ?? oldHeapLabel
          };
          newExpr = fseNew;
        }
      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr sse = (SeqSelectExpr)expr;
        Expression seq = Substitute(sse.Seq);
        Expression e0 = sse.E0 == null ? null : Substitute(sse.E0);
        Expression e1 = sse.E1 == null ? null : Substitute(sse.E1);
        if (seq != sse.Seq || e0 != sse.E0 || e1 != sse.E1) {
          newExpr = new SeqSelectExpr(sse.RangeToken, sse.SelectOne, seq, e0, e1, sse.CloseParen);
        }

      } else if (expr is SeqUpdateExpr) {
        var sse = (SeqUpdateExpr)expr;
        Expression seq = Substitute(sse.Seq);
        Expression index = Substitute(sse.Index);
        Expression val = Substitute(sse.Value);
        if (seq != sse.Seq || index != sse.Index || val != sse.Value) {
          newExpr = new SeqUpdateExpr(sse.RangeToken, seq, index, val);
        }
      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr mse = (MultiSelectExpr)expr;
        Expression array = Substitute(mse.Array);
        List<Expression> newArgs = SubstituteExprList(mse.Indices);
        if (array != mse.Array || newArgs != mse.Indices) {
          newExpr = new MultiSelectExpr(mse.RangeToken, array, newArgs);
        }

      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        Expression receiver = Substitute(e.Receiver);
        List<Expression> newArgs = SubstituteExprList(e.Args);
        var newTypeApplicationAtEnclosingClass = SubstituteTypeList(e.TypeApplication_AtEnclosingClass);
        var newTypeApplicationJustFunction = SubstituteTypeList(e.TypeApplication_JustFunction);
        if (receiver != e.Receiver || newArgs != e.Args ||
            newTypeApplicationAtEnclosingClass != e.TypeApplication_AtEnclosingClass ||
            newTypeApplicationJustFunction != e.TypeApplication_JustFunction) {
          FunctionCallExpr newFce = new FunctionCallExpr(expr.RangeToken, e.Name, receiver, newArgs, e.AtLabel ?? oldHeapLabel);
          newFce.Function = e.Function;  // resolve on the fly (and set newFce.Type below, at end)
          newFce.CoCall = e.CoCall;  // also copy the co-call status
          newFce.CoCallHint = e.CoCallHint;  // and any co-call hint
          newFce.TypeApplication_AtEnclosingClass = newTypeApplicationAtEnclosingClass;
          newFce.TypeApplication_JustFunction = newTypeApplicationJustFunction;
          newFce.IsByMethodCall = e.IsByMethodCall;
          newExpr = newFce;
        }

      } else if (expr is ApplyExpr) {
        ApplyExpr e = (ApplyExpr)expr;
        Expression fn = Substitute(e.Function);
        List<Expression> args = SubstituteExprList(e.Args);
        newExpr = new ApplyExpr(e.RangeToken, fn, args, e.CloseParen);

      } else if (expr is DatatypeValue) {
        var dtv = (DatatypeValue)expr;
        var newArguments = SubstituteExprList(dtv.Bindings.Arguments); // substitute into the expressions, but drop any binding names (since those are no longer needed)
        var newTypeArgs = SubstituteTypeList(dtv.InferredTypeArgs);
        if (newArguments != dtv.Bindings.Arguments || newTypeArgs != dtv.InferredTypeArgs) {
          var newDtv = new DatatypeValue(dtv.RangeToken, dtv.DatatypeName, dtv.MemberName, newArguments) {
            Ctor = dtv.Ctor,
            InferredTypeArgs = newTypeArgs
          };
          newExpr = newDtv;
        }

      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        // Note, it is up to the caller to avoid variable capture.  In most cases, this is not a
        // problem, since variables have unique declarations.  However, it is an issue if the substitution
        // takes place inside an OldExpr.  In those cases (see LetExpr), the caller can use a
        // BoogieWrapper before calling Substitute.
        Expression se = Substitute(e.E);
        if (se != e.E) {
          newExpr = new OldExpr(expr.RangeToken, se, e.At) {
            AtLabel = e.AtLabel ?? oldHeapLabel,
            Useless = e.Useless
          };
        }
      } else if (expr is UnchangedExpr) {
        var e = (UnchangedExpr)expr;
        var fr = new List<FrameExpression>();
        var anythingChanged = false;
        foreach (var fe in e.Frame) {
          var fefe = SubstFrameExpr(fe);
          if (fefe != fe) {
            anythingChanged = true;
          }
          fr.Add(fefe);
        }
        if (anythingChanged) {
          newExpr = new UnchangedExpr(e.RangeToken, fr, e.At) { AtLabel = e.AtLabel ?? oldHeapLabel };
        }
      } else if (expr is SeqConstructionExpr) {
        var e = (SeqConstructionExpr)expr;
        var sn = Substitute(e.N);
        var sinit = Substitute(e.Initializer);
        if (sn != e.N || sinit != e.Initializer) {
          newExpr = new SeqConstructionExpr(expr.RangeToken, e.ExplicitElementType, sn, sinit);
        }
      } else if (expr is MultiSetFormingExpr) {
        var e = (MultiSetFormingExpr)expr;
        var se = Substitute(e.E);
        if (se != e.E) {
          newExpr = new MultiSetFormingExpr(expr.RangeToken, se);
        }
      } else if (expr is BoxingCastExpr) {
        var e = (BoxingCastExpr)expr;
        var se = Substitute(e.E);
        var fromType = e.FromType.Subst(typeMap);
        var toType = e.ToType.Subst(typeMap);
        if (se != e.E || fromType != e.FromType || toType != e.ToType) {
          newExpr = new BoxingCastExpr(se, fromType, toType);
        }
      } else if (expr is UnaryExpr) {
        var e = (UnaryExpr)expr;
        var se = Substitute(e.E);
        if (e is TypeUnaryExpr typeUnaryExpr) {
          var toType = typeUnaryExpr.ToType.Subst(typeMap);
          if (se != e.E || toType != typeUnaryExpr.ToType) {
            if (e is ConversionExpr) {
              var ee = (ConversionExpr)e;
              newExpr = new ConversionExpr(expr.RangeToken, se, toType);
            } else if (e is TypeTestExpr) {
              var ee = (TypeTestExpr)e;
              newExpr = new TypeTestExpr(expr.RangeToken, se, toType);
            } else {
              Contract.Assert(false); // unexpected UnaryExpr subtype
            }
          }
        } else if (se != e.E) {
          if (e is FreshExpr) {
            var ee = (FreshExpr)e;
            newExpr = new FreshExpr(expr.RangeToken, se, ee.At) { AtLabel = ee.AtLabel ?? oldHeapLabel };
          } else if (e is UnaryOpExpr) {
            var ee = (UnaryOpExpr)e;
            newExpr = new UnaryOpExpr(expr.RangeToken, ee.Op, se);
          } else {
            Contract.Assert(false);  // unexpected UnaryExpr subtype
          }
        }

      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        Expression e0 = Substitute(e.E0);
        Expression e1 = Substitute(e.E1);
        if (e0 != e.E0 || e1 != e.E1) {
          BinaryExpr newBin = new BinaryExpr(expr.RangeToken, e.Op, e0, e1);
          newBin.ResolvedOp = e.ResolvedOp;  // part of what needs to be done to resolve on the fly (newBin.Type is set below, at end)
          newExpr = newBin;
        }

      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        var e0 = Substitute(e.E0);
        var e1 = Substitute(e.E1);
        var e2 = Substitute(e.E2);
        if (e0 != e.E0 || e1 != e.E1 || e2 != e.E2) {
          newExpr = new TernaryExpr(expr.RangeToken, e.Op, e0, e1, e2);
        }

      } else if (expr is LetExpr letExpr) {
        newExpr = LetExpr(letExpr);
      } else if (expr is NestedMatchExpr nestedMatchExpr) {
        var src = Substitute(nestedMatchExpr.Source);
        bool anythingChanged = src != nestedMatchExpr.Source;
        var flattened = nestedMatchExpr.Flattened == null ? null : Substitute(nestedMatchExpr.Flattened);
        anythingChanged |= flattened != nestedMatchExpr.Flattened;

        var cases = new List<NestedMatchCaseExpr>();
        foreach (var mc in nestedMatchExpr.Cases) {

          List<BoundVar> discoveredBvs = new();
          ExtendedPattern SubstituteForPattern(ExtendedPattern pattern) {
            switch (pattern) {
              case DisjunctivePattern disjunctivePattern:
                return new DisjunctivePattern(disjunctivePattern.RangeToken,
                  disjunctivePattern.Alternatives.Select(SubstituteForPattern).ToList(), disjunctivePattern.IsGhost);
              case IdPattern idPattern:
                if (idPattern.BoundVar == null) {
                  return new IdPattern(idPattern.RangeToken, idPattern.Id, idPattern.Type,
                    idPattern.Arguments.Select(SubstituteForPattern).ToList(), idPattern.IsGhost);
                }

                discoveredBvs.Add((BoundVar)idPattern.BoundVar);
                var result = new IdPattern(idPattern.RangeToken, idPattern.Id, idPattern.Type, null, idPattern.IsGhost) {
                  BoundVar = CreateBoundVarSubstitutions(new[] { (BoundVar)idPattern.BoundVar }.ToList(), false)[0]
                };
                if (idPattern.BoundVar != result.BoundVar) {
                  anythingChanged = true;
                }
                return result;
              case LitPattern litPattern:
                return litPattern;
              default:
                throw new ArgumentOutOfRangeException(nameof(pattern));
            }
          }
          var pattern = SubstituteForPattern(mc.Pat);
          var body = Substitute(mc.Body);
          // undo any changes to substMap (could be optimized to do this only if newBoundVars != mc.Arguments)
          foreach (var bv in discoveredBvs) {
            substMap.Remove(bv);
          }
          // Put things together
          if (body != mc.Body) {
            anythingChanged = true;
          }

          var newCaseExpr = new NestedMatchCaseExpr(mc.RangeToken, pattern, body, mc.Attributes);
          cases.Add(newCaseExpr);
        }
        if (anythingChanged) {
          newExpr = new NestedMatchExpr(expr.RangeToken, src, cases, nestedMatchExpr.UsesOptionalBraces) {
            Flattened = flattened
          };
        }

      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        var src = Substitute(e.Source);
        bool anythingChanged = src != e.Source;
        var cases = new List<MatchCaseExpr>();
        foreach (var mc in e.Cases) {
          var newBoundVars = CreateBoundVarSubstitutions(mc.Arguments, false);
          var body = Substitute(mc.Body);
          // undo any changes to substMap (could be optimized to do this only if newBoundVars != mc.Arguments)
          foreach (var bv in mc.Arguments) {
            substMap.Remove(bv);
          }
          // Put things together
          if (newBoundVars != mc.Arguments || body != mc.Body) {
            anythingChanged = true;
          }
          var newCaseExpr = new MatchCaseExpr(mc.RangeToken, mc.Ctor, mc.FromBoundVar, newBoundVars, body, mc.Attributes);
          newCaseExpr.Ctor = mc.Ctor;  // resolve here
          cases.Add(newCaseExpr);
        }
        if (anythingChanged) {
          var newME = new MatchExpr(expr.RangeToken, src, cases, e.UsesOptionalBraces);
          newME.MissingCases.AddRange(e.MissingCases);
          newExpr = newME;
        }

      } else if (expr is ComprehensionExpr) {

        newExpr = SubstituteComprehensionExpr((ComprehensionExpr)expr, true);

      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        newExpr = new StmtExpr(e.RangeToken, SubstStmt(e.S), Substitute(e.E));

      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        Expression test = Substitute(e.Test);
        Expression thn = Substitute(e.Thn);
        Expression els = Substitute(e.Els);
        if (test != e.Test || thn != e.Thn || els != e.Els) {
          newExpr = new ITEExpr(expr.RangeToken, e.IsBindingGuard, test, thn, els);
        }
      } else if (expr is ConcreteSyntaxExpression concreteSyntaxExpression) {
        Contract.Assert(concreteSyntaxExpression.ResolvedExpression != null);
        var resolvedExpression = Substitute(concreteSyntaxExpression.ResolvedExpression);
        return new ParensExpression(expr.RangeToken, resolvedExpression) {
          ResolvedExpression = resolvedExpression,
          RangeToken = expr.RangeToken,
          Type = resolvedExpression.Type
        };

      } else if (expr is Translator.BoogieFunctionCall) {
        var e = (Translator.BoogieFunctionCall)expr;
        bool anythingChanged = false;
        var newTyArgs = new List<Type>();
        foreach (var arg in e.TyArgs) {
          var newArg = arg.Subst(typeMap);
          if (newArg != arg) {
            anythingChanged = true;
          }
          newTyArgs.Add(newArg);
        }
        var newArgs = new List<Expression>();
        foreach (var arg in e.Args) {
          var newArg = Substitute(arg);
          if (newArg != arg) {
            anythingChanged = true;
          }
          newArgs.Add(newArg);
        }
        if (anythingChanged) {
          newExpr = new Translator.BoogieFunctionCall(e.RangeToken, e.FunctionName, e.UsesHeap, e.UsesOldHeap, e.HeapAtLabels, newArgs, newTyArgs);
        }

      } else {
        Contract.Assume(false); // unexpected Expression
      }

      if (newExpr == null) {
        return expr;
      } else {
        newExpr.Type = expr.Type.Subst(typeMap);  // resolve on the fly (any additional resolution must be done above)
        return newExpr;
      }
    }

    private Expression LetExpr(LetExpr letExpr) {
      if (letExpr.Exact) {
        var rhss = new List<Expression>();
        bool anythingChanged = false;
        foreach (var rhs in letExpr.RHSs) {
          var r = Substitute(rhs);
          if (r != rhs) {
            anythingChanged = true;
          }

          rhss.Add(r);
        }

        // Note, CreateBoundVarSubstitutions has the side effect of updating the substitution map.
        // For an Exact let expression, this is something that needs to be done after substituting
        // in the RHSs.
        var newCasePatterns = CreateCasePatternSubstitutions(letExpr.LHSs, true);
        if (newCasePatterns != letExpr.LHSs) {
          anythingChanged = true;
        }

        var body = Substitute(letExpr.Body);
        // undo any changes to substMap (could be optimized to do this only if newBoundVars != e.Vars)
        foreach (var bv in letExpr.BoundVars) {
          substMap.Remove(bv);
        }

        // Put things together
        if (anythingChanged || body != letExpr.Body) {
          return new LetExpr(letExpr.RangeToken, newCasePatterns, rhss, body, letExpr.Exact);
        }

        return null;
      } else {
        var rhs = Substitute(letExpr.RHSs[0]);
        var body = Substitute(letExpr.Body);
        var newBounds = SubstituteBoundedPoolList(letExpr.Constraint_Bounds);
        if (rhs == letExpr.RHSs[0] && body == letExpr.Body && newBounds == letExpr.Constraint_Bounds) {
          return null;
        }

        // keep copies of the substitution maps so we can reuse them at desugaring time
        var newSubstMap = new Dictionary<IVariable, Expression>(substMap);
        var newTypeMap = new Dictionary<TypeParameter, Type>(typeMap);
        return new Translator.SubstLetExpr(letExpr.RangeToken, letExpr.LHSs, new List<Expression> { rhs }, body, letExpr.Exact, letExpr, newSubstMap, newTypeMap, newBounds);
      }
    }

    /// <summary>
    /// This method calls "SubstituteBoundedPool" on each item in the possibly null list. If any of those calls returns a
    /// change from the original, then all of the results are returned in a new list; otherwise, "list" is returned.
    /// </summary>
    public List<ComprehensionExpr.BoundedPool>/*?*/ SubstituteBoundedPoolList(List<ComprehensionExpr.BoundedPool>/*?*/ list) {
      if (list != null) {
        var newList = list.ConvertAll(SubstituteBoundedPool);
        for (var i = 0; i < list.Count; i++) {
          if (list[i] != newList[i]) {
            return newList;
          }
        }
      }
      return list;
    }

    public ComprehensionExpr.BoundedPool SubstituteBoundedPool(ComprehensionExpr.BoundedPool bound) {
      if (bound == null) {
        return null;
      } else if (bound is ComprehensionExpr.ExactBoundedPool) {
        var b = (ComprehensionExpr.ExactBoundedPool)bound;
        return new ComprehensionExpr.ExactBoundedPool(Substitute(b.E));
      } else if (bound is ComprehensionExpr.BoolBoundedPool) {
        return bound;  // nothing to substitute
      } else if (bound is ComprehensionExpr.CharBoundedPool) {
        return bound;  // nothing to substitute
      } else if (bound is ComprehensionExpr.IntBoundedPool) {
        var b = (ComprehensionExpr.IntBoundedPool)bound;
        return new ComprehensionExpr.IntBoundedPool(b.LowerBound == null ? null : Substitute(b.LowerBound), b.UpperBound == null ? null : Substitute(b.UpperBound));
      } else if (bound is ComprehensionExpr.SetBoundedPool) {
        var b = (ComprehensionExpr.SetBoundedPool)bound;
        return new ComprehensionExpr.SetBoundedPool(Substitute(b.Set), b.BoundVariableType, b.CollectionElementType, b.IsFiniteCollection);
      } else if (bound is ComprehensionExpr.MultiSetBoundedPool) {
        var b = (ComprehensionExpr.MultiSetBoundedPool)bound;
        return new ComprehensionExpr.MultiSetBoundedPool(Substitute(b.MultiSet), b.BoundVariableType, b.CollectionElementType);
      } else if (bound is ComprehensionExpr.SubSetBoundedPool) {
        var b = (ComprehensionExpr.SubSetBoundedPool)bound;
        return new ComprehensionExpr.SubSetBoundedPool(Substitute(b.UpperBound), b.IsFiniteCollection);
      } else if (bound is ComprehensionExpr.SuperSetBoundedPool) {
        var b = (ComprehensionExpr.SuperSetBoundedPool)bound;
        return new ComprehensionExpr.SuperSetBoundedPool(Substitute(b.LowerBound));
      } else if (bound is ComprehensionExpr.MapBoundedPool) {
        var b = (ComprehensionExpr.MapBoundedPool)bound;
        return new ComprehensionExpr.MapBoundedPool(Substitute(b.Map), b.BoundVariableType, b.CollectionElementType, b.IsFiniteCollection);
      } else if (bound is ComprehensionExpr.SeqBoundedPool) {
        var b = (ComprehensionExpr.SeqBoundedPool)bound;
        return new ComprehensionExpr.SeqBoundedPool(Substitute(b.Seq), b.BoundVariableType, b.CollectionElementType);
      } else if (bound is ComprehensionExpr.DatatypeBoundedPool) {
        return bound;  // nothing to substitute
      } else if (bound is ComprehensionExpr.DatatypeInclusionBoundedPool) {
        return bound;  // nothing to substitute
      } else if (bound is ComprehensionExpr.AllocFreeBoundedPool) {
        return bound;  // nothing to substitute
      } else if (bound is ComprehensionExpr.ExplicitAllocatedBoundedPool) {
        return bound;  // nothing to substitute
      } else if (bound is AssignSuchThatStmt.WiggleWaggleBound) {
        return bound;  // nothing to substitute
      } else if (bound is ComprehensionExpr.SpecialAllocIndependenceAllocatedBoundedPool) {
        return bound;  // nothing to substitute
      } else if (bound is ComprehensionExpr.OlderBoundedPool) {
        return bound;  // nothing to substitute
      } else {
        Contract.Assume(false);  // unexpected ComprehensionExpr.BoundedPool
        throw new cce.UnreachableException();  // to please compiler
      }
    }

    /// <summary>
    /// Return a list of bound variables, of the same length as 'vars' but with possible substitutions.
    /// For any change necessary, update 'substMap' to reflect the new substitution; the caller is responsible for
    /// undoing these changes once the updated 'substMap' has been used.
    /// If no changes are necessary, the list returned is exactly 'vars' and 'substMap' is unchanged.
    /// </summary>
    protected virtual List<BoundVar> CreateBoundVarSubstitutions(List<BoundVar> vars, bool forceSubstitutionOfBoundVars) {
      bool anythingChanged = false;
      var newBoundVars = new List<BoundVar>();
      foreach (var bv in vars) {
        var tt = bv.Type.Subst(typeMap);
        if (!forceSubstitutionOfBoundVars && tt == bv.Type) {
          newBoundVars.Add(bv);
        } else {
          anythingChanged = true;
          var newBv = new BoundVar(bv.RangeToken, bv.Name, tt);
          newBoundVars.Add(newBv);
          // update substMap to reflect the new BoundVar substitutions
          var ie = new IdentifierExpr(newBv.RangeToken, newBv.Name);
          ie.Var = newBv;  // resolve here
          ie.Type = newBv.Type;  // resolve here
          substMap.Add(bv, ie);
        }
      }
      return anythingChanged ? newBoundVars : vars;
    }

    /// <summary>
    /// Return a list of local variables, of the same length as 'vars' but with possible substitutions.
    /// For any change necessary, update 'substMap' to reflect the new substitution; the caller is responsible for
    /// undoing these changes once the updated 'substMap' has been used.
    /// If no changes are necessary, the list returned is exactly 'vars' and 'substMap' is unchanged.
    /// </summary>
    protected virtual List<LocalVariable> CreateLocalVarSubstitutions(List<LocalVariable> vars, bool forceSubstitutionOfVars) {
      bool anythingChanged = false;
      var newVars = new List<LocalVariable>();
      foreach (var v in vars) {
        var tt = v.OptionalType.Subst(typeMap);
        if (!forceSubstitutionOfVars && tt == v.OptionalType) {
          newVars.Add(v);
        } else {
          anythingChanged = true;
          var newVar = new LocalVariable(v.RangeToken, v.Name, tt, v.IsGhost);
          newVar.type = tt;  // resolve here
          newVars.Add(newVar);
          // update substMap to reflect the new LocalVariable substitutions
          var ie = new IdentifierExpr(newVar.RangeToken, newVar.Name);
          ie.Var = newVar;  // resolve here
          ie.Type = newVar.Type;  // resolve here
          substMap.Add(v, ie);
        }
      }
      return anythingChanged ? newVars : vars;
    }

    /// <summary>
    /// Return a list of case patterns, of the same length as 'patterns' but with possible substitutions.
    /// For any change necessary, update 'substMap' to reflect the new substitution; the caller is responsible for
    /// undoing these changes once the updated 'substMap' has been used.
    /// If no changes are necessary, the list returned is exactly 'patterns' and 'substMap' is unchanged.
    /// </summary>
    protected virtual List<CasePattern<BoundVar>> CreateCasePatternSubstitutions(List<CasePattern<BoundVar>> patterns, bool forceSubstitutionOfBoundVars) {
      bool anythingChanged = false;
      var newPatterns = new List<CasePattern<BoundVar>>();
      foreach (var pat in patterns) {
        var newPat = SubstituteCasePattern(pat, forceSubstitutionOfBoundVars, CloneBoundVar);
        newPatterns.Add(newPat);
        if (newPat != pat) {
          anythingChanged = true;
        }
      }
      return anythingChanged ? newPatterns : patterns;
    }
    CasePattern<VT> SubstituteCasePattern<VT>(CasePattern<VT> pat, bool forceSubstitutionOfBoundVars,
        Func<CasePattern<VT>, Type, VT, VT> cloneVt
      ) where VT : class, IVariable {
      Contract.Requires(pat != null);
      if (pat.Var != null) {
        var bv = pat.Var;
        var tt = bv.Type.Subst(typeMap);
        if (forceSubstitutionOfBoundVars || tt != bv.Type) {
          var newBv = cloneVt(pat, tt, bv);
          // update substMap to reflect the new BoundVar substitutions
          var ie = new IdentifierExpr(newBv.RangeToken, newBv.Name);
          ie.Var = newBv;  // resolve here
          ie.Type = newBv.Type;  // resolve here
          substMap.Add(bv, ie);
          var newPat = new CasePattern<VT>(pat.RangeToken, newBv);
          newPat.AssembleExpr(null);
          return newPat;
        }
      } else if (pat.Arguments != null) {
        bool anythingChanged = false;
        var newArgs = new List<CasePattern<VT>>();
        foreach (var arg in pat.Arguments) {
          var newArg = SubstituteCasePattern(arg, forceSubstitutionOfBoundVars, cloneVt);
          newArgs.Add(newArg);
          if (newArg != arg) {
            anythingChanged = true;
          }
        }
        if (anythingChanged) {
          var patE = (DatatypeValue)pat.Expr;
          var newPat = new CasePattern<VT>(pat.RangeToken, pat.Id, newArgs);
          newPat.Ctor = pat.Ctor;
          newPat.AssembleExpr(patE.InferredTypeArgs.ConvertAll(tp => tp.Subst(typeMap)));
          return newPat;
        }
      }
      return pat;
    }

    protected List<Expression/*!*/>/*!*/ SubstituteExprList(List<Expression/*!*/>/*!*/ elist) {
      Contract.Requires(cce.NonNullElements(elist));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<Expression>>()));

      List<Expression> newElist = null;  // initialized lazily
      for (int i = 0; i < elist.Count; i++) {
        cce.LoopInvariant(newElist == null || newElist.Count == i);

        Expression substE = Substitute(elist[i]);
        if (substE != elist[i] && newElist == null) {
          newElist = new List<Expression>();
          for (int j = 0; j < i; j++) {
            newElist.Add(elist[j]);
          }
        }
        if (newElist != null) {
          newElist.Add(substE);
        }
      }
      if (newElist == null) {
        return elist;
      } else {
        return newElist;
      }
    }

    protected Dictionary<TypeParameter, Type> SubstituteTypeMap(Dictionary<TypeParameter, Type> tmap) {
      Contract.Requires(tmap != null);
      Contract.Ensures(Contract.Result<Dictionary<TypeParameter, Type>>() != null);
      if (typeMap.Count == 0) {  // optimization
        return tmap;
      }
      bool anythingChanged = false;
      var newTmap = new Dictionary<TypeParameter, Type>();
      var i = 0;
      foreach (var maplet in tmap) {
        var tt = maplet.Value.Subst(typeMap);
        if (tt != maplet.Value) {
          anythingChanged = true;
        }
        newTmap.Add(maplet.Key, tt);
        i++;
      }
      if (anythingChanged) {
        return newTmap;
      } else {
        return tmap;
      }
    }

    protected List<Type> SubstituteTypeList(List<Type> types) {
      Contract.Requires(types != null);
      Contract.Ensures(Contract.Result<List<Type>>() != null);
      if (types.Count == 0) {  // optimization
        return types;
      }
      bool anythingChanged = false;
      var newTypes = new List<Type>();
      var i = 0;
      foreach (var ty in types) {
        var tt = ty.Subst(typeMap);
        if (tt != ty) {
          anythingChanged = true;
        }
        newTypes.Add(tt);
        i++;
      }
      if (anythingChanged) {
        return newTypes;
      } else {
        return types;
      }
    }

    public LocalVariable CloneLocalVariable(CasePattern<LocalVariable> pat, Type tt, LocalVariable lv) {
      return new LocalVariable(pat.RangeToken, pat.Id, tt, lv.IsGhost);
    }
    public BoundVar CloneBoundVar(CasePattern<BoundVar> pat, Type tt, BoundVar bv) {
      return new BoundVar(pat.RangeToken, pat.Id, tt);
    }
    /// <summary>
    /// This method (which currently is used only internally to class Substituter) performs substitutions in
    /// statements that can occur in a StmtExpr.  (For example, it does not bother to do anything with a
    /// PrintStmt, ReturnStmt, or YieldStmt.)
    /// </summary>
    protected virtual Statement SubstStmt(Statement stmt) {
      Statement r;
      if (stmt == null) {
        return null;
      } else if (stmt is AssertStmt) {
        var s = (AssertStmt)stmt;
        r = new AssertStmt(s.RangeToken, Substitute(s.Expr), SubstBlockStmt(s.Proof), s.Label, SubstAttributes(s.Attributes));
      } else if (stmt is ExpectStmt) {
        var s = (ExpectStmt)stmt;
        r = new ExpectStmt(s.RangeToken, Substitute(s.Expr), Substitute(s.Message), SubstAttributes(s.Attributes));
      } else if (stmt is AssumeStmt) {
        var s = (AssumeStmt)stmt;
        r = new AssumeStmt(s.RangeToken, Substitute(s.Expr), SubstAttributes(s.Attributes));
      } else if (stmt is BreakStmt) {
        var s = (BreakStmt)stmt;
        BreakStmt rr;
        if (s.TargetLabel != null) {
          rr = new BreakStmt(s.RangeToken, s.TargetLabel, s.IsContinue);
        } else {
          rr = new BreakStmt(s.RangeToken, s.BreakAndContinueCount, s.IsContinue);
        }
        // r.TargetStmt will be filled in as later
        List<BreakStmt> breaks;
        if (!BreaksToBeResolved.TryGetValue(s, out breaks)) {
          breaks = new List<BreakStmt>();
          BreaksToBeResolved.Add(s, breaks);
        }
        breaks.Add(rr);
        r = rr;
      } else if (stmt is AssignStmt) {
        var s = (AssignStmt)stmt;
        r = new AssignStmt(s.RangeToken, Substitute(s.Lhs), SubstRHS(s.Rhs));
      } else if (stmt is CallStmt) {
        var s = (CallStmt)stmt;
        var rr = new CallStmt(s.RangeToken, s.Lhs.ConvertAll(Substitute), (MemberSelectExpr)Substitute(s.MethodSelect), s.Args.ConvertAll(Substitute));
        r = rr;
      } else if (stmt is DividedBlockStmt) {
        r = SubstDividedBlockStmt((DividedBlockStmt)stmt);
      } else if (stmt is BlockStmt) {
        r = SubstBlockStmt((BlockStmt)stmt);
      } else if (stmt is IfStmt) {
        var s = (IfStmt)stmt;
        var guard = s.IsBindingGuard ? SubstituteComprehensionExpr((ExistsExpr)s.Guard, false) : Substitute(s.Guard);
        r = new IfStmt(s.RangeToken, s.IsBindingGuard, guard, SubstBlockStmt(s.Thn), SubstStmt(s.Els));
      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        r = new AlternativeStmt(s.RangeToken, s.Alternatives.ConvertAll(SubstGuardedAlternative), s.UsesOptionalBraces);
      } else if (stmt is WhileStmt) {
        var s = (WhileStmt)stmt;
        r = new WhileStmt(s.RangeToken, Substitute(s.Guard), s.Invariants.ConvertAll(SubstMayBeFreeExpr), SubstSpecExpr(s.Decreases), SubstSpecFrameExpr(s.Mod), SubstBlockStmt(s.Body));
      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        r = new AlternativeLoopStmt(s.RangeToken, s.Invariants.ConvertAll(SubstMayBeFreeExpr), SubstSpecExpr(s.Decreases), SubstSpecFrameExpr(s.Mod), s.Alternatives.ConvertAll(SubstGuardedAlternative), s.UsesOptionalBraces);
      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        var newBoundVars = CreateBoundVarSubstitutions(s.BoundVars, false);
        var body = SubstStmt(s.Body);
        // undo any changes to substMap (could be optimized to do this only if newBoundVars != e.Vars)
        foreach (var bv in s.BoundVars) {
          substMap.Remove(bv);
        }

        // Put things together
        var rr = new ForallStmt(s.RangeToken, newBoundVars, SubstAttributes(s.Attributes), Substitute(s.Range), s.Ens.ConvertAll(SubstMayBeFreeExpr), body);
        rr.Kind = s.Kind;
        rr.CanConvert = s.CanConvert;
        rr.Bounds = SubstituteBoundedPoolList(s.Bounds);
        if (s.ForallExpressions != null) {
          rr.ForallExpressions = s.ForallExpressions.ConvertAll(Substitute);
        }
        r = rr;
      } else if (stmt is CalcStmt) {
        var s = (CalcStmt)stmt;
        var rr = new CalcStmt(s.RangeToken, SubstCalcOp(s.UserSuppliedOp), s.Lines.ConvertAll(Substitute), s.Hints.ConvertAll(SubstBlockStmt), s.StepOps.ConvertAll(SubstCalcOp), SubstAttributes(s.Attributes));
        rr.Op = SubstCalcOp(s.Op);
        rr.Steps.AddRange(s.Steps.ConvertAll(Substitute));
        rr.Result = Substitute(s.Result);
        r = rr;
      } else if (stmt is MatchStmt) {
        var s = (MatchStmt)stmt;
        var rr = new MatchStmt(s.RangeToken, Substitute(s.Source), s.Cases.ConvertAll(SubstMatchCaseStmt), s.UsesOptionalBraces);
        rr.MissingCases.AddRange(s.MissingCases);
        r = rr;
      } else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        r = new AssignSuchThatStmt(s.RangeToken, s.Lhss.ConvertAll(Substitute), Substitute(s.Expr), s.AssumeToken == null ? null : s.AssumeToken, null);
      } else if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        var resolved = s.ResolvedStatements;
        UpdateStmt rr;
        if (resolved.Count == 1) {
          // when later translating this UpdateStmt, the s.Lhss and s.Rhss components won't be used, only s.ResolvedStatements
          rr = new UpdateStmt(s.RangeToken, s.Lhss, s.Rhss, s.CanMutateKnownState);
        } else {
          rr = new UpdateStmt(s.RangeToken, s.Lhss.ConvertAll(Substitute), s.Rhss.ConvertAll(SubstRHS), s.CanMutateKnownState);
        }

        if (s.ResolvedStatements != null) {
          rr.ResolvedStatements = s.ResolvedStatements.ConvertAll(SubstStmt);
        }
        r = rr;
      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        var lhss = CreateLocalVarSubstitutions(s.Locals, false);
        var rr = new VarDeclStmt(s.RangeToken, lhss, (ConcreteUpdateStatement)SubstStmt(s.Update));
        r = rr;
      } else if (stmt is VarDeclPattern) {
        var s = (VarDeclPattern)stmt;
        var lhss = SubstituteCasePattern(s.LHS, false, CloneLocalVariable);
        var rr = new VarDeclPattern(s.RangeToken, lhss, (Expression)Substitute(s.RHS), s.HasGhostModifier);
        r = rr;
      } else if (stmt is RevealStmt) {
        var s = (RevealStmt)stmt;
        // don't need to substitute s.Expr since it won't be used, only the s.ResolvedStatements are used.
        var rr = new RevealStmt(s.RangeToken, s.Exprs);
        rr.LabeledAsserts.AddRange(s.LabeledAsserts);
        rr.ResolvedStatements.AddRange(s.ResolvedStatements.ConvertAll(SubstStmt));
        r = rr;
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
      }

      // add labels to the cloned statement
      AddStmtLabels(r, stmt.Labels);
      r.Attributes = SubstAttributes(stmt.Attributes);
      r.IsGhost = stmt.IsGhost;
      if (stmt.Labels != null || stmt is WhileStmt) {
        List<BreakStmt> breaks;
        if (BreaksToBeResolved.TryGetValue(stmt, out breaks)) {
          foreach (var b in breaks) {
            b.TargetStmt = r;
          }
          BreaksToBeResolved.Remove(stmt);
        }
      }

      return r;
    }

    Dictionary<Statement, List<BreakStmt>> BreaksToBeResolved = new Dictionary<Statement, List<BreakStmt>>();  // old-target -> new-breaks

    protected void AddStmtLabels(Statement s, LList<Label> node) {
      if (node != null) {
        AddStmtLabels(s, node.Next);
        s.Labels = new LList<Label>(node.Data, s.Labels);
      }
    }

    protected virtual DividedBlockStmt SubstDividedBlockStmt(DividedBlockStmt stmt) {
      return stmt == null ? null : new DividedBlockStmt(stmt.RangeToken, stmt.BodyInit.ConvertAll(SubstStmt), stmt.SeparatorTok, stmt.BodyProper.ConvertAll(SubstStmt));
    }

    protected virtual BlockStmt SubstBlockStmt(BlockStmt stmt) {
      if (stmt == null) {
        return null;
      }
      var prevSubstMap = new Dictionary<IVariable, Expression>(substMap);
      var b = new BlockStmt(stmt.RangeToken, stmt.Body.ConvertAll(SubstStmt));
      if (substMap.Count != prevSubstMap.Count) {
        // reset substMap to what it was (note that substMap is a readonly field, so we can't just change it back to prevSubstMap)
        substMap.Clear();
        foreach (var item in prevSubstMap) {
          substMap.Add(item.Key, item.Value);
        }
      }
      return b;
    }

    protected GuardedAlternative SubstGuardedAlternative(GuardedAlternative alt) {
      Contract.Requires(alt != null);
      var guard = alt.IsBindingGuard ? SubstituteComprehensionExpr((ExistsExpr)alt.Guard, false) : Substitute(alt.Guard);
      return new GuardedAlternative(alt.RangeToken, alt.IsBindingGuard, guard, alt.Body.ConvertAll(SubstStmt));
    }

    protected AttributedExpression SubstMayBeFreeExpr(AttributedExpression expr) {
      Contract.Requires(expr != null);
      var mfe = new AttributedExpression(Substitute(expr.E));
      mfe.Attributes = SubstAttributes(expr.Attributes);
      return mfe;
    }

    protected Specification<Expression> SubstSpecExpr(Specification<Expression> spec) {
      var ee = spec.Expressions == null ? null : spec.Expressions.ConvertAll(Substitute);
      return new Specification<Expression>(ee, SubstAttributes(spec.Attributes));
    }

    protected Specification<FrameExpression> SubstSpecFrameExpr(Specification<FrameExpression> frame) {
      var ee = frame.Expressions == null ? null : frame.Expressions.ConvertAll(SubstFrameExpr);
      return new Specification<FrameExpression>(ee, SubstAttributes(frame.Attributes));
    }

    public FrameExpression SubstFrameExpr(FrameExpression frame) {
      Contract.Requires(frame != null);
      var fe = new FrameExpression(frame.RangeToken, Substitute(frame.E), frame.FieldName);
      fe.Field = frame.Field;  // resolve here
      return fe;
    }

    protected AssignmentRhs SubstRHS(AssignmentRhs rhs) {
      AssignmentRhs c;
      if (rhs is ExprRhs) {
        var r = (ExprRhs)rhs;
        c = new ExprRhs(Substitute(r.Expr));
      } else if (rhs is HavocRhs) {
        c = new HavocRhs(rhs.RangeToken);
      } else {
        // since the Substituter is assumed to operate on statements only if they are part of a StatementExpression, then the TypeRhs case cannot occur
        Contract.Assume(false); throw new cce.UnreachableException();
      }
      c.Attributes = SubstAttributes(rhs.Attributes);
      return c;
    }

    protected MatchCaseStmt SubstMatchCaseStmt(MatchCaseStmt c) {
      Contract.Requires(c != null);
      var newBoundVars = CreateBoundVarSubstitutions(c.Arguments, false);
      var r = new MatchCaseStmt(c.RangeToken, c.Ctor, c.FromBoundVar, newBoundVars, c.Body.ConvertAll(SubstStmt), c.Attributes);
      r.Ctor = c.Ctor;
      // undo any changes to substMap (could be optimized to do this only if newBoundVars != e.Vars)
      foreach (var bv in c.Arguments) {
        substMap.Remove(bv);
      }
      return r;
    }

    protected CalcStmt.CalcOp SubstCalcOp(CalcStmt.CalcOp op) {
      if (op == null) {
        return null;
      } else if (op is CalcStmt.BinaryCalcOp) {
        return new CalcStmt.BinaryCalcOp(((CalcStmt.BinaryCalcOp)op).Op);
      } else if (op is CalcStmt.TernaryCalcOp) {
        return new CalcStmt.TernaryCalcOp(Substitute(((CalcStmt.TernaryCalcOp)op).Index));
      } else {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }
    }

    public Attributes SubstAttributes(Attributes attrs) {
      Contract.Requires(cce.NonNullDictionaryAndValues(substMap));
      if (attrs != null) {
        var newArgs = new List<Expression>();  // allocate it eagerly, what the heck, it doesn't seem worth the extra complexity in the code to do it lazily for the infrequently occurring attributes
        bool anyArgSubst = false;
        foreach (var arg in attrs.Args) {
          var argToBeAdded = arg;
          var substArg = Substitute(arg);
          if (substArg != arg) {
            argToBeAdded = substArg;
            anyArgSubst = true;
          }
          newArgs.Add(argToBeAdded);
        }
        if (!anyArgSubst) {
          newArgs = attrs.Args;
        }

        Attributes prev = SubstAttributes(attrs.Prev);
        if (newArgs != attrs.Args || prev != attrs.Prev) {
          if (attrs is UserSuppliedAttributes) {
            var usa = (UserSuppliedAttributes)attrs;
            return new UserSuppliedAttributes(usa.Tok, usa.OpenBrace, usa.CloseBrace, newArgs, prev);
          } else {
            return new Attributes(attrs.Name, newArgs, prev);
          }
        }
      }
      return attrs;
    }

    /// <summary>
    /// Substitution in a comprehension expression. 
    /// Parameter 'forceSubstituteOfBoundVars' should be set to false if and only if
    /// the expression is a binding guard, in which case a bound variable is introduced.
    /// Such a variable must not be substituted. 
    /// </summary>
    protected Expression SubstituteComprehensionExpr(ComprehensionExpr expr, bool forceSubstituteOfBoundVars) {

      Expression newExpr = null;

      var e = (ComprehensionExpr)expr;
      // For quantifiers and setComprehesion we want to make sure that we don't introduce name clashes with
      // the enclosing scopes.

      var q = e as QuantifierExpr;
      if (q != null && q.SplitQuantifier != null) {
        if (forceSubstituteOfBoundVars) {
          return Substitute(q.SplitQuantifierExpression);
        } else {
          return SubstituteComprehensionExpr((ComprehensionExpr)q.SplitQuantifierExpression, false);
        }
      }

      var newBoundVars = CreateBoundVarSubstitutions(e.BoundVars, forceSubstituteOfBoundVars && (expr is ForallExpr || expr is ExistsExpr || expr is SetComprehension));
      var newRange = e.Range == null ? null : Substitute(e.Range);
      var newTerm = Substitute(e.Term);
      var newAttrs = SubstAttributes(e.Attributes);
      var newBounds = SubstituteBoundedPoolList(e.Bounds);
      if (newBoundVars != e.BoundVars || newRange != e.Range || newTerm != e.Term || newAttrs != e.Attributes ||
          newBounds != e.Bounds || !forceSubstituteOfBoundVars) {
        if (e is SetComprehension) {
          newExpr = new SetComprehension(e.RangeToken, ((SetComprehension)e).Finite, newBoundVars,
            newRange, newTerm, newAttrs);
        } else if (e is MapComprehension) {
          var mc = (MapComprehension)e;
          var newTermLeft = mc.IsGeneralMapComprehension ? Substitute(mc.TermLeft) : null;
          newExpr = new MapComprehension(e.RangeToken, mc.Finite, newBoundVars, newRange, newTermLeft, newTerm, newAttrs);
        } else if (expr is ForallExpr forallExpr) {
          newExpr = new ForallExpr(expr.RangeToken, newBoundVars, newRange, newTerm, newAttrs);
        } else if (expr is ExistsExpr existsExpr) {
          newExpr = new ExistsExpr(expr.RangeToken, newBoundVars, newRange, newTerm, newAttrs);
        } else if (expr is LambdaExpr) {
          var l = (LambdaExpr)expr;
          newExpr = new LambdaExpr(e.RangeToken, newBoundVars, newRange,
            l.Reads.ConvertAll(SubstFrameExpr), newTerm);
        } else {
          Contract.Assert(false); // unexpected ComprehensionExpr
        }

        ((ComprehensionExpr)newExpr).Bounds = newBounds;
      }

      // undo any changes to substMap (could be optimized to do this only if newBoundVars != e.BoundVars)
      foreach (var bv in e.BoundVars) {
        substMap.Remove(bv);
      }

      return newExpr;

    }

  }
}

