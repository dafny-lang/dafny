using System.Collections.Generic;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public abstract class TypeWithMembersSymbolBase<TNode> : Symbol, ILocalizableSymbol where TNode : TopLevelDeclWithMembers {
    public TNode Declaration { get; }
    public object Node => Declaration;

    public IList<ISymbol> Members { get; } = new List<ISymbol>();

    public override IEnumerable<ISymbol> Children => Members;

    protected TypeWithMembersSymbolBase(ISymbol? scope, TNode declaration) : base(scope, declaration.Name) {
      Declaration = declaration;
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"{Declaration.WhatKind} {Declaration.Name}";
    }
  }
}
