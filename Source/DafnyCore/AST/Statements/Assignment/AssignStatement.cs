#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// Parsed from ":="
/// </summary>
public class AssignStatement : ConcreteAssignStatement, ICloneable<AssignStatement>, ICanResolve {
  public List<AssignmentRhs> Rhss;
  public bool CanMutateKnownState;
  public Expression? OriginalInitialLhs = null;

  [FilledInDuringResolution] public List<Statement>? ResolvedStatements;
  public override IEnumerable<Statement> SubStatements => Children.OfType<Statement>();

  public override IEnumerable<Expression> NonSpecificationSubExpressions =>
    ResolvedStatements == null ? Rhss.SelectMany(r => r.NonSpecificationSubExpressions) : [];

  public override IEnumerable<INode> Children => ResolvedStatements ?? Lhss.Concat<Node>(Rhss);
  public override IEnumerable<INode> PreResolveChildren => Lhss.Concat<Node>(Rhss);

  public override IEnumerable<Statement> PreResolveSubStatements => [];

  public override IEnumerable<IdentifierExpr> GetAssignedLocals() {
    return ResolvedStatements!.SelectMany(r => r.GetAssignedLocals());
  }

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Lhss));
    Contract.Invariant(cce.NonNullElements(Rhss));
  }

  public AssignStatement Clone(Cloner cloner) {
    return new AssignStatement(cloner, this);
  }

  public AssignStatement(Cloner cloner, AssignStatement original) : base(cloner, original) {
    Rhss = original.Rhss.Select(cloner.CloneRHS).ToList();
    CanMutateKnownState = original.CanMutateKnownState;
    if (cloner.CloneResolvedFields) {
      ResolvedStatements = original.ResolvedStatements?.Select(stmt => cloner.CloneStmt(stmt, false)).ToList();
    }
  }

  public AssignStatement(IOrigin origin, List<Expression> lhss, List<AssignmentRhs> rhss)
    : base(origin, lhss) {
    Contract.Requires(cce.NonNullElements(lhss));
    Contract.Requires(cce.NonNullElements(rhss));
    Contract.Requires(lhss.Count != 0 || rhss.Count == 1);
    Rhss = rhss;
    CanMutateKnownState = false;
  }

  [SyntaxConstructor]
  public AssignStatement(IOrigin origin, List<Expression> lhss, List<AssignmentRhs> rhss, bool canMutateKnownState,
    Attributes? attributes = null)
    : base(origin, lhss, attributes) {
    Contract.Requires(cce.NonNullElements(lhss));
    Contract.Requires(cce.NonNullElements(rhss));
    Contract.Requires(lhss.Count != 0 || rhss.Count == 1);
    Rhss = rhss;
    CanMutateKnownState = canMutateKnownState;
  }

  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      foreach (var e in base.PreResolveSubExpressions) {
        yield return e;
      }
      foreach (var rhs in Rhss) {
        foreach (var e in rhs.PreResolveSubExpressions) {
          yield return e;
        }
      }
    }
  }

  /// <summary>
  /// Resolve the RHSs and entire UpdateStmt (LHSs should already have been checked by the caller).
  /// errorCountBeforeCheckingLhs is passed in so that this method can determined if any resolution errors were found during
  /// LHS or RHS checking, because only if no errors were found is update.ResolvedStmt changed.
  /// </summary>
  public override void Resolve(ModuleResolver resolver, ResolutionContext resolutionContext) {
    Contract.Requires(this != null);
    Contract.Requires(resolutionContext != null);

    int errorCountBeforeCheckingLhs = resolver.Reporter.Count(ErrorLevel.Error);

    base.Resolve(resolver, resolutionContext);

    IOrigin? firstEffectfulRhs = null;
    MethodCallInformation? methodCallInfo = null;
    ResolvedStatements = [];
    foreach (var rhs in Rhss) {
      bool isEffectful;
      if (rhs is TypeRhs) {
        var tr = (TypeRhs)rhs;
        resolver.ResolveTypeRhs(tr, this, resolutionContext);
        isEffectful = (tr is AllocateClass { InitCall: not null });
      } else if (rhs is HavocRhs) {
        isEffectful = false;
      } else {
        var er = (ExprRhs)rhs;
        if (er.Expr is ApplySuffix) {
          var a = (ApplySuffix)er.Expr;
          var cRhs = resolver.ResolveApplySuffix(a, resolutionContext, true);
          isEffectful = cRhs != null;
          methodCallInfo = methodCallInfo ?? cRhs;
        } else {
          resolver.ResolveExpression(er.Expr, resolutionContext);
          isEffectful = false;
        }
      }
      if (isEffectful && firstEffectfulRhs == null) {
        firstEffectfulRhs = rhs.Origin;
      }

      resolver.ResolveAttributes(rhs, resolutionContext);
    }

    // figure out what kind of UpdateStmt this is
    if (firstEffectfulRhs == null) {
      if (Lhss.Count == 0) {
        Contract.Assert(Rhss.Count == 1);  // guaranteed by the parser
        resolver.Reporter.Error(MessageSource.Resolver, this, "expected method call, found expression");
      } else if (Lhss.Count != Rhss.Count) {
        resolver.Reporter.Error(MessageSource.Resolver, this, "the number of left-hand sides ({0}) and right-hand sides ({1}) must match for a multi-assignment", Lhss.Count, Rhss.Count);
      } else if (resolver.Reporter.Count(ErrorLevel.Error) == errorCountBeforeCheckingLhs) {
        // add the statements here in a sequence, but don't use that sequence later for translation (instead, should translate properly as multi-assignment)
        for (int i = 0; i < Lhss.Count; i++) {
          var origin = Lhss.Count > 1 ? new OverrideCenter(Origin, Rhss[i].ReportingRange) : Origin;
          var a = new SingleAssignStmt(origin, Lhss[i].Resolved, Rhss[i]);
          ResolvedStatements.Add(a);
        }
      }

    } else if (CanMutateKnownState) {
      if (1 < Rhss.Count) {
        resolver.Reporter.Error(MessageSource.Resolver, firstEffectfulRhs, "cannot have effectful parameter in multi-return statement.");
      } else { // it might be ok, if it is a TypeRhs
        Contract.Assert(Rhss.Count == 1);
        if (methodCallInfo != null) {
          resolver.Reporter.Error(MessageSource.Resolver, methodCallInfo.Tok, "cannot have method call in return statement.");
        } else {
          // we have a TypeRhs
          Contract.Assert(Rhss[0] is TypeRhs);
          var tr = (TypeRhs)Rhss[0];
          if (tr.CanAffectPreviouslyKnownExpressions) {
            resolver.Reporter.Error(MessageSource.Resolver, tr.Origin, "can only have initialization methods which modify at most 'this'.");
          } else if (resolver.Reporter.Count(ErrorLevel.Error) == errorCountBeforeCheckingLhs) {
            var a = new SingleAssignStmt(Origin, Lhss[0].Resolved, tr);
            ResolvedStatements.Add(a);
          }
        }
      }

    } else {
      // if there was an effectful RHS, that must be the only RHS
      if (Rhss.Count != 1) {
        resolver.Reporter.Error(MessageSource.Resolver, firstEffectfulRhs, "an update statement is allowed an effectful RHS only if there is just one RHS");
      } else if (methodCallInfo == null) {
        // must be a single TypeRhs
        if (Lhss.Count != 1) {
          Contract.Assert(2 <= Lhss.Count);  // the parser allows 0 Lhss only if the whole statement looks like an expression (not a TypeRhs)
          resolver.Reporter.Error(MessageSource.Resolver, Lhss[1].Origin, "the number of left-hand sides ({0}) and right-hand sides ({1}) must match for a multi-assignment", Lhss.Count, Rhss.Count);
        } else if (resolver.Reporter.Count(ErrorLevel.Error) == errorCountBeforeCheckingLhs) {
          var a = new SingleAssignStmt(Origin, Lhss[0].Resolved, Rhss[0]);
          ResolvedStatements.Add(a);
        }
      } else if (resolver.Reporter.Count(ErrorLevel.Error) == errorCountBeforeCheckingLhs) {
        // a call statement
        var resolvedLhss = new List<Expression>();
        foreach (var ll in Lhss) {
          resolvedLhss.Add(ll.Resolved);
        }
        CallStmt a = new CallStmt(Origin, resolvedLhss, methodCallInfo.Callee, methodCallInfo.ActualParameters, methodCallInfo.Tok.ReportingRange);
        a.OriginalInitialLhs = OriginalInitialLhs;
        ResolvedStatements.Add(a);
      }
    }

    foreach (var a in ResolvedStatements) {
      resolver.ResolveStatement(a, resolutionContext);
    }
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext,
    string? proofContext, bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    ResolvedStatements!.ForEach(ss => ss.ResolveGhostness(resolver, reporter, mustBeErasable, codeContext,
      proofContext, allowAssumptionVariables, inConstructorInitializationPhase));
    IsGhost = ResolvedStatements.All(ss => ss.IsGhost);
  }
}