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
  public override IEnumerable<INode> ConcreteChildren => Children;

  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations() {
    return new IDeclarationOrUsage[] { Ctor }.Where(x => x != null);
  }

  public IToken NameToken => Tok;
}