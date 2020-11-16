namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class ScopeSymbol : Symbol {
    public ScopeSymbol(ISymbol? scope) : base(scope, string.Empty) {
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
