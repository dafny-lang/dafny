using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class NestedMatchCaseStmt : NestedMatchCase, IAttributeBearingDeclaration, ICloneable<NestedMatchCaseStmt> {
  public readonly List<Statement> Body;
  public Attributes Attributes;
  Attributes IAttributeBearingDeclaration.Attributes => Attributes;
  public NestedMatchCaseStmt(RangeToken rangeToken, ExtendedPattern pat, List<Statement> body) : base(rangeToken.StartToken, pat) {
    RangeToken = rangeToken;
    Contract.Requires(body != null);
    this.Body = body;
    this.Attributes = null;
  }
  public NestedMatchCaseStmt(IToken tok, ExtendedPattern pat, List<Statement> body, Attributes attrs) : base(tok, pat) {
    Contract.Requires(body != null);
    this.Body = body;
    this.Attributes = attrs;
  }

  private NestedMatchCaseStmt(Cloner cloner, NestedMatchCaseStmt original) : base(original.tok, original.Pat) {
    this.Body = original.Body.Select(cloner.CloneStmt).ToList();
    this.Attributes = cloner.CloneAttributes(original.Attributes);
  }

  public NestedMatchCaseStmt Clone(Cloner cloner) {
    return new NestedMatchCaseStmt(cloner, this);
  }
  public override IEnumerable<Node> Children => new[] { Pat }.Concat<Node>(Body).Concat(Attributes?.Args ?? Enumerable.Empty<Node>());
  public override IEnumerable<Node> PreResolveChildren => Children;

  public void Resolve(
    Resolver resolver,
    ResolutionContext resolutionContext,
    Dictionary<TypeParameter, Type> subst,
    Type sourceType) {
    var beforeResolveErrorCount = resolver.reporter.ErrorCount;

    var boundVars = Pat.ReplaceTypesWithBoundVariables(resolver, resolutionContext).ToList();
    foreach (var boundVar in boundVars) {
      var localVariable = new LocalVariable(boundVar.var.RangeToken, boundVar.var.Name, boundVar.var.Type, boundVar.var.IsGhost);
      var casePattern = new CasePattern<LocalVariable>(localVariable.RangeToken.EndToken, localVariable);
      var varDecl = new VarDeclPattern(localVariable.Tok.ToRange(), casePattern, boundVar.usage, false);
      Body.Insert(0, varDecl);
    }

    Pat.Resolve(resolver, resolutionContext, sourceType, resolutionContext.IsGhost, true, false, false);
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
