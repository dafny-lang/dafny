using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class NestedMatchCaseStmt : NestedMatchCase, IAttributeBearingDeclaration {
  public readonly List<Statement> Body;
  public Attributes Attributes;
  Attributes IAttributeBearingDeclaration.Attributes => Attributes;
  public NestedMatchCaseStmt(IToken tok, ExtendedPattern pat, List<Statement> body) : base(tok, pat) {
    Contract.Requires(body != null);
    this.Body = body;
    this.Attributes = null;
  }
  public NestedMatchCaseStmt(IToken tok, ExtendedPattern pat, List<Statement> body, Attributes attrs) : base(tok, pat) {
    Contract.Requires(body != null);
    this.Body = body;
    this.Attributes = attrs;
  }

  public override IEnumerable<INode> Children => new[] { Pat }.Concat<INode>(Body).Concat(Attributes?.Args ?? Enumerable.Empty<INode>());

  public void Resolve(
    Resolver resolver,
    ResolutionContext resolutionContext,
    Dictionary<TypeParameter, Type> subst,
    Type sourceType) {
    var beforeResolveErrorCount = resolver.reporter.ErrorCount;

    var boundVars = Pat.ReplaceTypesWithBoundVariables(resolver, resolutionContext).ToList();
    foreach (var boundVar in boundVars) {
      var localVariable = new LocalVariable(boundVar.var.Tok, boundVar.var.Tok, boundVar.var.Name, boundVar.var.Type, boundVar.var.IsGhost);
      var casePattern = new CasePattern<LocalVariable>(localVariable.EndTok, localVariable);
      var varDecl = new VarDeclPattern(localVariable.Tok, localVariable.Tok, casePattern, boundVar.usage, false);
      Body.Insert(0, varDecl);
    }

    Pat.Resolve(resolver, resolutionContext, subst, sourceType, resolutionContext.IsGhost, true);
    resolver.ResolveAttributes(this, resolutionContext);
    var afterResolveErrorCount = resolver.reporter.ErrorCount;
    if (beforeResolveErrorCount == afterResolveErrorCount) {
      resolver.DominatingStatementLabels.PushMarker();
      foreach (Statement ss in Body) {
        resolver.ResolveStatementWithLabels(ss, resolutionContext);
      }
      resolver.DominatingStatementLabels.PopMarker();
    }
  }
}
