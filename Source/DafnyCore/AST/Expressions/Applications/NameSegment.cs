#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class NameSegment : ConcreteSyntaxExpression, ICloneable<NameSegment>, ICanFormat {
  public string Name;
  public Name NameNode => new Name(Origin, Name);
  public List<Type>? OptTypeArguments;

  [SyntaxConstructor]
  public NameSegment(IOrigin origin, string name, List<Type>? optTypeArguments)
    : base(origin) {
    Contract.Requires(optTypeArguments == null || optTypeArguments.Count > 0);
    Name = name;
    OptTypeArguments = optTypeArguments;
  }

  public NameSegment(Cloner cloner, NameSegment original) : base(cloner, original) {
    Name = original.Name;
    OptTypeArguments = original.OptTypeArguments?.ConvertAll(cloner.CloneType);
  }

  public NameSegment Clone(Cloner cloner) {
    return new NameSegment(cloner, this);
  }

  public override IEnumerable<INode> PreResolveChildren => OptTypeArguments ?? [];
  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    formatter.SetTypeLikeIndentation(indentBefore, OwnedTokens);
    foreach (var subType in PreResolveChildren.OfType<Type>()) {
      formatter.SetTypeIndentation(subType);
    }
    return false;
  }
}