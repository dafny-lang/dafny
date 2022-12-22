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

  public override IEnumerable<INode> Children => Arguments ?? Enumerable.Empty<INode>();

  public override void Resolve(Resolver resolver, ResolutionContext resolutionContext,
    IDictionary<TypeParameter, Type> subst, Type sourceType, bool isGhost, bool mutable,
    bool inPattern, bool inDisjunctivePattern) {

    if (inDisjunctivePattern && ResolvedLit == null && Arguments == null && !IsWildcardPattern) {
      resolver.reporter.Error(MessageSource.Resolver, Tok, "Disjunctive patterns may not bind variables");
    }
    
    Debug.Assert(Arguments != null || Type is InferredTypeProxy);

    if (Arguments == null) {
      Type substitutedSourceType = sourceType.Subst(subst);
      Type = substitutedSourceType; // Only possible because we did a rewrite one level higher, which used the information from Type.
      //BoundVar = new Formal(Tok, Id, substitutedSourceType, false, isGhost, null); 
      if (mutable) {
        var localVariable = new LocalVariable(Tok, Tok, Id, null, isGhost);
        localVariable.type = substitutedSourceType;
        BoundVar = localVariable;
      } else {
        var boundVar = new BoundVar(Tok, Id, substitutedSourceType);
        boundVar.IsGhost = isGhost;
        BoundVar = boundVar;
      }

      resolver.scope.Push(Id, BoundVar);
      resolver.ResolveType(Tok, BoundVar.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);

    } else {
      if (Ctor != null) {
        subst = TypeParameter.SubstitutionMap(Ctor.EnclosingDatatype.TypeArgs, sourceType.NormalizeExpand().TypeArgs);
        for (var index = 0; index < Arguments.Count; index++) {
          var argument = Arguments[index];
          var formal = Ctor.Formals[index];
          argument.Resolve(resolver, resolutionContext, subst, formal.Type.Subst(subst), formal.IsGhost, mutable, true, inDisjunctivePattern);
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
}
