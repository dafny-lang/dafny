﻿using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class FieldSymbol : MemberSymbol, ILocalizableSymbol {
    public Field Declaration { get; }
    public INode Node => Declaration;

    public FieldSymbol(ILegacySymbol? scope, Field field) : base(scope, field) {
      Declaration = field;
    }

    public string GetDetailText(DafnyOptions options, CancellationToken cancellationToken) {
      var prefix = Declaration.IsMutable ? "var" : "const";
      return $"{prefix} {TypePrefix}{Declaration.Name}: {Declaration.Type}";
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
