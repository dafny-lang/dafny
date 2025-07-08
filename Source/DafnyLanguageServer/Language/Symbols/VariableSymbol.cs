﻿using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class VariableSymbol : Symbol, ILocalizableSymbol {
    public IVariable Declaration { get; }
    public INode Node => Declaration;

    public VariableSymbol(ILegacySymbol? scope, IVariable variable) : base(scope, variable.Name) {
      Declaration = variable;
    }

    public string GetDetailText(DafnyOptions options, CancellationToken cancellationToken) {
      return Declaration.AsText();
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
