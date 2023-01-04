using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class NestedMatchStmt : Statement, ICloneable<NestedMatchStmt> {
  public readonly Expression Source;
  public readonly List<NestedMatchCaseStmt> Cases;
  public readonly bool UsesOptionalBraces;

  [FilledInDuringResolution] public Statement Flattened { get; set; }

  private void InitializeAttributes() {
    // Default case for match is false
    bool splitMatch = Attributes.Contains(this.Attributes, "split");
    Attributes.ContainsBool(this.Attributes, "split", ref splitMatch);
    foreach (var c in this.Cases) {
      if (!Attributes.Contains(c.Attributes, "split")) {
        List<Expression> args = new List<Expression>();
        args.Add(new LiteralExpr(c.Tok, splitMatch));
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
      Flattened = cloner.CloneStmt(original.Flattened);
    }
  }

  public override IEnumerable<INode> Children => new[] { Source }.Concat<INode>(Cases);

  public override IEnumerable<Statement> SubStatements => Cases.SelectMany(c => c.Body);

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) {
        yield return e;
      }
      yield return Source;
    }
  }
  public NestedMatchStmt(IToken tok, IToken endTok, Expression source, [Captured] List<NestedMatchCaseStmt> cases, bool usesOptionalBraces, Attributes attrs = null)
    : base(tok, endTok, attrs) {
    Contract.Requires(source != null);
    Contract.Requires(cce.NonNullElements(cases));
    this.Source = source;
    this.Cases = cases;
    this.UsesOptionalBraces = usesOptionalBraces;
    InitializeAttributes();
  }

  public void Resolve(Resolver resolver, ResolutionContext resolutionContext) {

    resolver.ResolveExpression(Source, resolutionContext);

    if (Source.Type is TypeProxy) {
      resolver.PartiallySolveTypeConstraints(true);

      if (Source.Type is TypeProxy) {
        resolver.reporter.Error(MessageSource.Resolver, Tok, "Could not resolve the type of the source of the match expression. Please provide additional typing annotations.");
        return;
      }
    }

    var errorCount = resolver.reporter.Count(ErrorLevel.Error);
    var sourceType = resolver.PartiallyResolveTypeForMemberSelection(Source.tok, Source.Type).NormalizeExpand();
    this.CheckLinearNestedMatchStmt(sourceType, resolutionContext, resolver);
    if (resolver.reporter.Count(ErrorLevel.Error) != errorCount) {
      return;
    }

    var dtd = sourceType.AsDatatype;
    var subst = new Dictionary<TypeParameter, Type>();
    if (dtd != null) {
      // build the type-parameter substitution map for this use of the datatype
      subst = TypeParameter.SubstitutionMap(dtd.TypeArgs, sourceType.TypeArgs);
    }

    foreach (var _case in Cases) {
      resolver.scope.PushMarker();
      _case.Resolve(resolver, resolutionContext, subst, sourceType);
      resolver.scope.PopMarker();
    }
  }

  public void CheckLinearNestedMatchStmt(Type dtd, ResolutionContext resolutionContext, Resolver resolver) {
    foreach (NestedMatchCaseStmt mc in this.Cases) {
      resolver.scope.PushMarker();
      resolver.ResolveAttributes(mc, resolutionContext);
      mc.CheckLinearNestedMatchCase(dtd, resolutionContext, resolver);
      resolver.scope.PopMarker();
    }
  }
}
