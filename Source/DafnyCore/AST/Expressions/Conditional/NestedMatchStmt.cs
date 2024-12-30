using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class NestedMatchStmt : Statement, ICloneable<NestedMatchStmt>, ICanFormat, INestedMatch, ICanResolve {
  public Expression Source { get; }
  public string MatchTypeName => "statement";
  public List<NestedMatchCaseStmt> Cases { get; }

  IReadOnlyList<NestedMatchCase> INestedMatch.Cases => Cases;

  public readonly bool UsesOptionalBraces;

  [FilledInDuringResolution] public Statement Flattened { get; set; }

  private void InitializeAttributes() {
    // Default case for match is false
    bool splitMatch = Attributes.Contains(Attributes, "split");
    Attributes.ContainsBool(Attributes, "split", ref splitMatch);
    foreach (var c in Cases) {
      if (!Attributes.Contains(c.Attributes, "split")) {
        List<Expression> args = new List<Expression>();
        args.Add(Expression.CreateBoolLiteral(c.Tok, splitMatch));
        Attributes attrs = new Attributes("split", args, c.Attributes);
        c.Attributes = attrs;
      }
    }
  }

  public NestedMatchStmt Clone(Cloner cloner) {
    return new NestedMatchStmt(cloner, this);
  }

  public NestedMatchStmt(Cloner cloner, NestedMatchStmt original) : base(cloner, original) {
    Source = cloner.CloneExpr(original.Source);
    Cases = original.Cases.ConvertAll(cloner.CloneNestedMatchCaseStmt);
    UsesOptionalBraces = original.UsesOptionalBraces;
    if (cloner.CloneResolvedFields) {
      Flattened = cloner.CloneStmt(original.Flattened, false);
    }
  }

  public override IEnumerable<INode> Children => new[] { Source }.Concat<Node>(Cases);

  public override IEnumerable<Statement> SubStatements {
    get {
      if (Flattened != null) {
        return Flattened.SubStatements;
      }
      return Cases.SelectMany(c => c.Body);
    }
  }

  public override IEnumerable<Statement> PreResolveSubStatements {
    get => Cases.SelectMany(oneCase => oneCase.Body);
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) {
        yield return e;
      }
      yield return Source;
      foreach (var mc in Cases) {
        foreach (var ee in mc.Pat.SubExpressions) {
          yield return ee;
        }
      }
    }
  }

  public NestedMatchStmt(IOrigin rangeOrigin, Expression source, [Captured] List<NestedMatchCaseStmt> cases, bool usesOptionalBraces, Attributes attrs = null)
    : base(rangeOrigin, attrs) {
    Contract.Requires(source != null);
    Contract.Requires(cce.NonNullElements(cases));
    Source = source;
    Cases = cases;
    UsesOptionalBraces = usesOptionalBraces;
    InitializeAttributes();
  }

  /// <summary>
  /// Resolves a NestedMatchStmt by
  /// 1 - checking that all of its patterns are linear
  /// 2 - desugaring it into a decision tree of MatchStmt and IfStmt (for constant matching)
  /// 3 - resolving the generated (sub)statement.
  /// </summary>
  public void Resolve(ModuleResolver resolver, ResolutionContext resolutionContext) {
    resolver.ResolveExpression(Source, resolutionContext);

    if (Source.Type is TypeProxy) {
      resolver.PartiallySolveTypeConstraints(true);

      if (Source.Type is TypeProxy) {
        resolver.Reporter.Error(MessageSource.Resolver, Tok, "Could not resolve the type of the source of the match statement. Please provide additional typing annotations.");
        return;
      }
    }

    var errorCount = resolver.Reporter.Count(ErrorLevel.Error);
    var sourceType = resolver.PartiallyResolveTypeForMemberSelection(Source.Tok, Source.Type).NormalizeExpand();
    CheckLinearNestedMatchStmt(sourceType, resolutionContext, resolver);
    if (resolver.Reporter.Count(ErrorLevel.Error) != errorCount) {
      return;
    }

    var dtd = sourceType.AsDatatype;
    var subst = new Dictionary<TypeParameter, Type>();
    if (dtd != null) {
      // build the type-parameter substitution map for this use of the datatype
      subst = TypeParameter.SubstitutionMap(dtd.TypeArgs, sourceType.TypeArgs);
    }

    foreach (var _case in Cases) {
      resolver.Scope.PushMarker();
      _case.Resolve(resolver, resolutionContext, subst, sourceType);
      resolver.Scope.PopMarker();
    }
  }

  public void CheckLinearNestedMatchStmt(Type dtd, ResolutionContext resolutionContext, ModuleResolver resolver) {
    foreach (NestedMatchCaseStmt mc in Cases) {
      resolver.scope.PushMarker();
      resolver.ResolveAttributes(mc, resolutionContext);
      mc.CheckLinearNestedMatchCase(dtd, resolutionContext, resolver);
      resolver.scope.PopMarker();
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentCases(indentBefore, OwnedTokens.Concat(Cases.SelectMany(oneCase => oneCase.OwnedTokens)).OrderBy(token => token.pos), () => {
      foreach (var e in PreResolveSubExpressions) {
        formatter.Visit(e, indentBefore);
      }
      foreach (var s in PreResolveSubStatements) {
        formatter.Visit(s, indentBefore);
      }
    });
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext, string proofContext,
    bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    var hasGhostPattern = Cases.
      SelectMany(caze => caze.Pat.DescendantsAndSelf)
      .OfType<IdPattern>().Any(idPattern => idPattern.Ctor != null && idPattern.Ctor.IsGhost);
    IsGhost = mustBeErasable || ExpressionTester.UsesSpecFeatures(Source) || hasGhostPattern;

    foreach (var kase in Cases) {
      ExpressionTester.MakeGhostAsNeeded(kase.Pat, IsGhost);
    }

    if (!mustBeErasable && IsGhost) {
      reporter.Info(MessageSource.Resolver, Tok, "ghost match");
    }

    Cases.ForEach(kase => kase.Body.ForEach(ss =>
      ss.ResolveGhostness(resolver, reporter, IsGhost, codeContext,
      proofContext, allowAssumptionVariables, inConstructorInitializationPhase)));
    IsGhost = IsGhost || Cases.All(kase => kase.Body.All(ss => ss.IsGhost));
    if (!IsGhost) {
      // If there were features in the source expression that are treated differently in ghost and non-ghost
      // contexts, make sure they get treated for non-ghost use.
      ExpressionTester.CheckIsCompilable(resolver, reporter, Source, codeContext);
    }
  }
}
