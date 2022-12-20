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

  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations() {
    return new IDeclarationOrUsage[] { Ctor }.Where(x => x != null);
  }

  public IToken NameToken => Tok;
}
