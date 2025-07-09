using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class DatatypeUpdateExpr : ConcreteSyntaxExpression, IHasReferences, ICloneable<DatatypeUpdateExpr> {
  public Expression Root;
  public List<Tuple<Token, string, Expression>> Updates;
  [FilledInDuringResolution] public List<MemberDecl> Members;
  [FilledInDuringResolution] public List<DatatypeCtor> LegalSourceConstructors;
  [FilledInDuringResolution] public bool InCompiledContext;
  [FilledInDuringResolution] public Expression ResolvedCompiledExpression; // see comment for Resolver.ResolveDatatypeUpdate

  public DatatypeUpdateExpr Clone(Cloner cloner) {
    return new DatatypeUpdateExpr(cloner, this);
  }

  public DatatypeUpdateExpr(Cloner cloner, DatatypeUpdateExpr original) : base(cloner, original) {
    Root = cloner.CloneExpr(original.Root);
    Updates = original.Updates.Select(t => Tuple.Create(t.Item1, t.Item2, cloner.CloneExpr(t.Item3)))
      .ToList();

    if (cloner.CloneResolvedFields) {
      Members = original.Members;
      LegalSourceConstructors = original.LegalSourceConstructors;
      InCompiledContext = original.InCompiledContext;
      if (original.ResolvedExpression == original.ResolvedCompiledExpression) {
        ResolvedCompiledExpression = ResolvedExpression;
      } else {
        ResolvedCompiledExpression = cloner.CloneExpr(original.ResolvedCompiledExpression);
      }
    }
  }

  public DatatypeUpdateExpr(IOrigin origin, Expression root, List<Tuple<Token, string, Expression>> updates)
    : base(origin) {
    Contract.Requires(origin != null);
    Contract.Requires(root != null);
    Contract.Requires(updates != null);
    Contract.Requires(updates.Count != 0);
    Root = root;
    Updates = updates;
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      if (ResolvedExpression == null) {
        Contract.Assert(ResolvedCompiledExpression == null);
        foreach (var preResolved in PreResolveSubExpressions) {
          yield return preResolved;
        }
      } else {
        foreach (var e in base.SubExpressions) {
          yield return e;
        }
        if (ResolvedExpression != ResolvedCompiledExpression) {
          yield return ResolvedCompiledExpression;
        }
      }
    }
  }

  public IEnumerable<Reference> GetReferences() {
    return LegalSourceConstructors == null ? []
      : Updates.Zip(LegalSourceConstructors).Select(t =>
        new Reference(new TokenRange(t.First.Item1, t.First.Item1),
          t.Second.Formals.Find(f => f.Name == t.First.Item2)));
  }

  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      yield return Root;
      foreach (var update in Updates) {
        yield return update.Item3;
      }
    }
  }
}