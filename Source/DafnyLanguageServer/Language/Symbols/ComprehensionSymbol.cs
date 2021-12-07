using System.Collections.Generic;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class ComprehensionSymbol : ScopeSymbol, ILocalizableSymbol {
    private readonly ComprehensionExpr comprehension;
    public ComprehensionSymbol(ISymbol? scope, ComprehensionExpr comprehension) : base(scope, comprehension) {
      this.comprehension = comprehension;
    }

    public override string GetDetailText(CancellationToken cancellationToken) {
      return $"{comprehension.WhatKind} ({comprehension.BoundVars.AsCommaSeperatedText()}): {comprehension.Type.AsText()}";
    }
  }
}