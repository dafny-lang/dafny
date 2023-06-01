using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class DatatypeUpdateExpr : ConcreteSyntaxExpression, IHasUsages, ICloneable<DatatypeUpdateExpr> {
  public readonly Expression Root;
  public readonly List<Tuple<IToken, string, Expression>> Updates;
  [FilledInDuringResolution] public List<MemberDecl> Members;
  [FilledInDuringResolution] public List<DatatypeCtor> LegalSourceConstructors;
  [FilledInDuringResolution] public bool InCompiledContext;
  [FilledInDuringResolution] public Expression ResolvedCompiledExpression; // see comment for Resolver.ResolveDatatypeUpdate

  public DatatypeUpdateExpr Clone(Cloner cloner) {
    return new DatatypeUpdateExpr(cloner, this);
  }

  public DatatypeUpdateExpr(Cloner cloner, DatatypeUpdateExpr original) : base(cloner, original) {
    Root = cloner.CloneExpr(original.Root);
    Updates = original.Updates.Select(t => Tuple.Create<IToken, string, Expression>(cloner.Tok((IToken)t.Item1), t.Item2, cloner.CloneExpr(t.Item3)))
      .ToList();

    if (cloner.CloneResolvedFields) {
      Members = original.Members;
      LegalSourceConstructors = original.LegalSourceConstructors;
      InCompiledContext = original.InCompiledContext;
      ResolvedCompiledExpression = cloner.CloneExpr(original.ResolvedCompiledExpression);
    }
  }

  public DatatypeUpdateExpr(IToken tok, Expression root, List<Tuple<IToken, string, Expression>> updates)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(root != null);
    Contract.Requires(updates != null);
    Contract.Requires(updates.Count != 0);
    Root = root;
    Updates = updates;
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      if (ResolvedExpression == null) {
        foreach (var preResolved in PreResolveSubExpressions) {

          yield return preResolved;
        }
      } else {
        foreach (var e in base.SubExpressions) {
          yield return e;
        }
      }
    }
  }

  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations() {
    return LegalSourceConstructors;
  }

  public IToken NameToken => tok;

  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      yield return Root;
      foreach (var update in Updates) {
        yield return update.Item3;
      }
    }
  }
}