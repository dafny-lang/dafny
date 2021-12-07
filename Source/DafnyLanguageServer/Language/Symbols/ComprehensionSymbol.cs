using System.Collections.Generic;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class ComprehensionSymbol : Symbol, ILocalizableSymbol {
    public ComprehensionExpr Declaration { get; }
    public object Node => Declaration;

    public IList<VariableSymbol> BoundVars { get; } = new List<VariableSymbol>();

    public override IEnumerable<ISymbol> Children => BoundVars;

    public ComprehensionSymbol(ISymbol? scope, ComprehensionExpr comprehension) : base(scope, "") {
      Declaration = comprehension;
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"{Declaration.WhatKind} ({Declaration.BoundVars.AsCommaSeperatedText()}): {Declaration.Type.AsText()}";
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}