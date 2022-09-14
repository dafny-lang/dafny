using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class IdPattern : ExtendedPattern, IHasUsages {
  public bool HasParenthesis { get; }
  public readonly String Id;
  public readonly Type Type; // This is the syntactic type, ExtendedPatterns dissapear during resolution.
  public List<ExtendedPattern> Arguments; // null if just an identifier; possibly empty argument list if a constructor call
  public LiteralExpr ResolvedLit; // null if just an identifier
  [FilledInDuringResolution]
  public DatatypeCtor Ctor;

  public bool IsWildcardPattern =>
    Arguments == null && Id.StartsWith("_");

  public void MakeAConstructor() {
    this.Arguments = new List<ExtendedPattern>();
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
    IDictionary<TypeParameter, Type> subst, Type sourceType, bool isGhost) {

    if (Arguments == null) {
      var boundVar = new BoundVar(Tok, Id, Resolver.SubstType(Type, subst));
      resolver.scope.Push(Id, boundVar);
      resolver.ResolveType(boundVar.tok, boundVar.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
      Type substitutedSourceType = Resolver.SubstType(sourceType, subst);

      var errorMsgWithToken = new TypeConstraint.ErrorMsgWithToken(Tok, "the declared type of the formal ({0}) does not agree with the corresponding type in the constructor's signature ({1})", boundVar.Type, substitutedSourceType);
      resolver.ConstrainSubtypeRelation(boundVar.Type, substitutedSourceType, errorMsgWithToken, true);
      boundVar.IsGhost = isGhost;
    } else {
      if (Ctor != null) {
        for (var index = 0; index < Arguments.Count; index++) {
          var argument = Arguments[index];
          var formal = Ctor.Formals[index];
          argument.Resolve(resolver, resolutionContext, subst, formal.Type, formal.IsGhost);
        }
      }
    }
  }

  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations() {
    return new IDeclarationOrUsage[] { Ctor }.Where(x => x != null);
  }

  public IToken NameToken => Tok;
}