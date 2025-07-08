﻿using System.Collections.Generic;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public abstract class TypeWithMembersSymbolBase : Symbol, ILocalizableSymbol {
    public abstract INode Node { get; }

    public IList<ILegacySymbol> Members { get; } = new List<ILegacySymbol>();

    public override IEnumerable<ILegacySymbol> Children => Members;

    protected TypeWithMembersSymbolBase(ILegacySymbol? scope, string name) : base(scope, name) { }

    public abstract string GetDetailText(DafnyOptions options, CancellationToken cancellationToken);
  }

  public abstract class TypeWithMembersSymbolBase<TNode> : TypeWithMembersSymbolBase where TNode : TopLevelDeclWithMembers {
    public TNode Declaration { get; }
    public override Node Node => Declaration;

    protected TypeWithMembersSymbolBase(ILegacySymbol? scope, TNode declaration) : base(scope, declaration.Name) {
      Declaration = declaration;
    }

    public override string GetDetailText(DafnyOptions options, CancellationToken cancellationToken) {
      return $"{Declaration.WhatKind} {Declaration.Name}";
    }
  }
}
