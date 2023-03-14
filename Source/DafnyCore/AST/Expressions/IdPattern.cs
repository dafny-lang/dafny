using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Security.AccessControl;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Microsoft.Dafny;

public class IdPattern : ExtendedPattern, IHasUsages {
  public bool HasParenthesis { get; }
  public String Id;
  public Type Type; // This is the syntactic type, ExtendedPatterns dissapear during resolution.
  public IVariable BoundVar { get; set; }
  public List<ExtendedPattern> Arguments; // null if just an identifier; possibly empty argument list if a constructor call
  public LiteralExpr ResolvedLit; // null if just an identifier
  [FilledInDuringResolution]
  public DatatypeCtor Ctor;

  public bool IsWildcardPattern =>
    Arguments == null && Id.StartsWith("_");

  public void MakeAConstructor() {
    this.Arguments = new List<ExtendedPattern>();
  }

  public IdPattern(Cloner cloner, IdPattern original) : base(cloner.Tok(original.Tok), original.IsGhost) {
    Id = original.Id;
    Arguments = original.Arguments?.Select(cloner.CloneExtendedPattern).ToList();
    HasParenthesis = original.HasParenthesis;
    if (cloner.CloneResolvedFields) {
      BoundVar = cloner.CloneIVariable(original.BoundVar, false);
      Type = original.Type;
    } else {
      Type = new InferredTypeProxy();
    }
  }

  public IdPattern(IToken tok, String id, List<ExtendedPattern> arguments, bool isGhost = false, bool hasParenthesis = false) : base(tok, isGhost) {
    Contract.Requires(id != null);
    Contract.Requires(arguments != null); // Arguments can be empty, but shouldn't be null
    HasParenthesis = hasParenthesis;
    this.Id = id;
    this.Type = new InferredTypeProxy();
    this.Arguments = arguments;
  }

  public IdPattern(IToken tok, String id, Type type, List<ExtendedPattern> arguments, bool isGhost = false) : base(tok, isGhost) {
    Contract.Requires(id != null);
    Contract.Requires(arguments != null); // Arguments can be empty, but shouldn't be null
    this.Id = id;
    this.Type = type == null ? new InferredTypeProxy() : type;
    this.Arguments = arguments;
    this.IsGhost = isGhost;
  }

  public override string ToString() {
    if (Arguments == null || Arguments.Count == 0) {
      return Id;
    } else {
      List<string> cps = Arguments.ConvertAll<string>(x => x.ToString());
      return string.Format("{0}({1})", Id, String.Join(", ", cps));
    }
  }

  public override IEnumerable<Node> Children => Arguments ?? Enumerable.Empty<Node>();
  public override IEnumerable<Node> PreResolveChildren => Children;

  public override void Resolve(Resolver resolver, ResolutionContext resolutionContext,
    Type sourceType, bool isGhost, bool mutable,
    bool inPattern, bool inDisjunctivePattern) {

    if (inDisjunctivePattern && ResolvedLit == null && Arguments == null && !IsWildcardPattern) {
      resolver.reporter.Error(MessageSource.Resolver, Tok, "Disjunctive patterns may not bind variables");
    }

    Debug.Assert(Arguments != null || Type is InferredTypeProxy);

    if (Arguments == null) {
      Type = sourceType; // Possible because we did a rewrite one level higher, which copied the syntactic type information to a let.
      if (mutable) {
        var localVariable = new LocalVariable(RangeToken, Id, null, isGhost);
        localVariable.type = sourceType;
        BoundVar = localVariable;
      } else {
        var boundVar = new BoundVar(Tok, Id, sourceType);
        boundVar.IsGhost = isGhost;
        BoundVar = boundVar;
      }

      resolver.scope.Push(Id, BoundVar);
      resolver.ResolveType(Tok, BoundVar.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);

    } else {
      if (Ctor != null) {
        var subst = TypeParameter.SubstitutionMap(sourceType.AsDatatype.TypeArgs, sourceType.NormalizeExpand().TypeArgs);
        for (var index = 0; index < Arguments.Count; index++) {
          var argument = Arguments[index];
          var formal = Ctor.Formals[index];
          argument.Resolve(resolver, resolutionContext, formal.Type.Subst(subst), formal.IsGhost, mutable, true, inDisjunctivePattern);
        }
      }
    }
  }

  public override IEnumerable<(BoundVar var, Expression usage)> ReplaceTypesWithBoundVariables(Resolver resolver,
    ResolutionContext resolutionContext) {
    if (Arguments == null && Type is not InferredTypeProxy) {
      var freshName = resolver.FreshTempVarName(Id, resolutionContext.CodeContext);
      var boundVar = new BoundVar(Tok, Id, Type);
      boundVar.IsGhost = IsGhost;
      yield return (boundVar, new IdentifierExpr(Tok, freshName));
      Id = freshName;
      Type = new InferredTypeProxy();
    }

    if (Arguments != null) {
      foreach (var childResult in Arguments.SelectMany(a => a.ReplaceTypesWithBoundVariables(resolver, resolutionContext))) {
        yield return childResult;
      }
    }
  }

  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations() {
    return new IDeclarationOrUsage[] { Ctor }.Where(x => x != null);
  }

  public IToken NameToken => Tok;

  public void CheckLinearVarPattern(Type type, ResolutionContext resolutionContext, Resolver resolver) {
    if (Arguments != null) {
      if (Id == BuiltIns.TupleTypeCtorName(1)) {
        resolver.reporter.Error(MessageSource.Resolver, this.Tok, "parentheses are not allowed around a pattern");
      } else {
        resolver.reporter.Error(MessageSource.Resolver, this.Tok, "member {0} does not exist in type {1}", this.Id, type);
      }
      return;
    }

    if (resolver.scope.FindInCurrentScope(this.Id) != null) {
      resolver.reporter.Error(MessageSource.Resolver, this.Tok, "Duplicate parameter name: {0}", this.Id);
    } else if (IsWildcardPattern) {
      // Wildcard, ignore
      return;
    } else {
      NameSegment e = new NameSegment(this.Tok, this.Id, null);
      resolver.ResolveNameSegment(e, true, null, resolutionContext, false, false);
      if (e.ResolvedExpression == null) {
        resolver.ScopePushAndReport(resolver.scope, new BoundVar(this.Tok, this.Id, type), "parameter");
      } else {
        // finds in full scope, not just current scope
        if (e.Resolved is MemberSelectExpr mse) {
          if (mse.Member.IsStatic && mse.Member is ConstantField cf) {
            Expression c = cf.Rhs;
            if (c is LiteralExpr lit) {
              this.ResolvedLit = lit;
              if (type.Equals(e.ResolvedExpression.Type)) {
                // OK - type is correct
              } else {
                // may well be a proxy so add a type constraint
                resolver.ConstrainSubtypeRelation(e.ResolvedExpression.Type, type, this.Tok,
                  "the type of the pattern ({0}) does not agree with the match expression ({1})", e.ResolvedExpression.Type, type);
              }
            } else {
              resolver.reporter.Error(MessageSource.Resolver, this.Tok, "{0} is not initialized as a constant literal", this.Id);
              resolver.ScopePushAndReport(resolver.scope, new BoundVar(this.Tok, this.Id, type), "parameter");
            }
          } else {
            // Not a static const, so just a variable
            resolver.ScopePushAndReport(resolver.scope, new BoundVar(this.Tok, this.Id, type), "parameter");
          }
        } else {
          resolver.ScopePushAndReport(resolver.scope, new BoundVar(this.Tok, this.Id, type), "parameter");
        }
      }
    }
  }
}
