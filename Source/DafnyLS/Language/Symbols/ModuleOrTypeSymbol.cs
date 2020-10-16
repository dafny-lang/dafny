using System.Collections.Generic;

namespace DafnyLS.Language.Symbols {
  internal class ModuleOrTypeSymbol : ISymbol {
    public string Identifier => throw new System.NotImplementedException();

    public IEnumerable<ISymbol> Children => throw new System.NotImplementedException();

    public ISymbol? Scope => throw new System.NotImplementedException();

    public TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      throw new System.NotImplementedException();
    }
  }
}
