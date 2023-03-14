using System.Collections.Generic;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public abstract class TypeWithMembersSymbolBase : Symbol, ILocalizableSymbol {
    public abstract object Node { get; }

    public IList<ISymbol> Members { get; } = new List<ISymbol>();

    public override IEnumerable<ISymbol> Children => Members;

    protected TypeWithMembersSymbolBase(ISymbol? scope, string name) : base(scope, name) { }

    public abstract string GetDetailText(DafnyOptions options, CancellationToken cancellationToken);
  }

  public abstract class TypeWithMembersSymbolBase<TNode> : TypeWithMembersSymbolBase where TNode : TopLevelDeclWithMembers {
    public TNode Declaration { get; }
    public override object Node => Declaration;

    protected TypeWithMembersSymbolBase(ISymbol? scope, TNode declaration) : base(scope, declaration.Name) {
      Declaration = declaration;
    }

    public override string GetDetailText(DafnyOptions options, CancellationToken cancellationToken) {
      return $"{Declaration.WhatKind} {Declaration.Name}";
    }
  }
}
