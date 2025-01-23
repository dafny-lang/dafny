using System.Collections.Generic;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public abstract class TypeWithMembersSymbolBase(ILegacySymbol? scope, string name)
    : Symbol(scope, name), ILocalizableSymbol {
    public abstract INode Node { get; }

    public IList<ILegacySymbol> Members { get; } = new List<ILegacySymbol>();

    public override IEnumerable<ILegacySymbol> Children => Members;

    public abstract string GetDetailText(DafnyOptions options, CancellationToken cancellationToken);
  }

  public abstract class TypeWithMembersSymbolBase<TNode>(ILegacySymbol? scope, TNode declaration)
    : TypeWithMembersSymbolBase(scope, declaration.Name)
    where TNode : TopLevelDeclWithMembers {
    public TNode Declaration { get; } = declaration;
    public override Node Node => Declaration;

    public override string GetDetailText(DafnyOptions options, CancellationToken cancellationToken) {
      return $"{Declaration.WhatKind} {Declaration.Name}";
    }
  }
}
