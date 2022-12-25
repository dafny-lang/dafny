using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class NestedMatchExpr : Expression {
  public readonly Expression Source;
  public readonly List<NestedMatchCaseExpr> Cases;
  public readonly bool UsesOptionalBraces;
  public Attributes Attributes;
  
  [FilledInDuringResolution]
  public Expression Denested { get; set; }

  public NestedMatchExpr(IToken tok, Expression source, [Captured] List<NestedMatchCaseExpr> cases, bool usesOptionalBraces, Attributes attrs = null) : base(tok) {
    Contract.Requires(source != null);
    Contract.Requires(cce.NonNullElements(cases));
    this.Source = source;
    this.Cases = cases;
    this.UsesOptionalBraces = usesOptionalBraces;
    this.Attributes = attrs;
  }

  public override IEnumerable<Expression> SubExpressions =>
    new[] { Source }.Concat(Cases.Select(c => c.Body));

  public override IEnumerable<INode> Children => new[] { Source }.Concat<INode>(Cases);

  public void Resolve(Resolver resolver, ResolutionContext resolutionContext) {

    resolver.ResolveExpression(Source, resolutionContext);

    bool debug = DafnyOptions.O.MatchCompilerDebug;
    if (Source.Type is TypeProxy) {
      resolver.PartiallySolveTypeConstraints(true);
      if (debug) {
        Console.WriteLine("DEBUG: Type of {0} was still a proxy, solving type constraints results in type {1}", Printer.ExprToString(Source), Source.Type.ToString());
      }

      if (Source.Type is TypeProxy) {
        resolver.reporter.Error(MessageSource.Resolver, tok, "Could not resolve the type of the source of the match expression. Please provide additional typing annotations.");
        return;
      }
    }

    var errorCount = resolver.reporter.Count(ErrorLevel.Error);
    var sourceType = resolver.PartiallyResolveTypeForMemberSelection(Source.tok, Source.Type).NormalizeExpand();
    if (resolver.reporter.Count(ErrorLevel.Error) != errorCount) {
      return;
    }

    if (debug) {
      Console.WriteLine("DEBUG: {0} ResolveNestedMatchExpr  1 - Checking Linearity of patterns", tok.line);
    }
    resolver.CheckLinearNestedMatchExpr(sourceType, this, resolutionContext);
    if (resolver.reporter.Count(ErrorLevel.Error) != errorCount) {
      return;
    }

    var dtd = sourceType.AsDatatype;
    var subst = new Dictionary<TypeParameter, Type>();
    if (dtd != null) {
      Contract.Assert(sourceType != null); // dtd and sourceType are set together above
      var ctors = dtd.ConstructorsByName;
      Contract.Assert(ctors !=
                      null); // dtd should have been inserted into datatypeCtors during a previous resolution stage

      // build the type-parameter substitution map for this use of the datatype
      subst = TypeParameter.SubstitutionMap(dtd.TypeArgs, sourceType.TypeArgs);
    }

    Type = new InferredTypeProxy();
    foreach (var _case in Cases) {
      resolver.scope.PushMarker();
      _case.Resolve(resolver, resolutionContext, subst, Type, sourceType);
      resolver.scope.PopMarker();
    }
  }
}
