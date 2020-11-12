using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class FieldSymbol : Symbol, ILocalizableSymbol {
    public Field Declaration { get; }
    public object Node => Declaration;

    public FieldSymbol(ISymbol? scope, Field field) : base(scope, field.Name) {
      Declaration = field;
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      var prefix = Declaration.IsMutable ? "var" : "const";
      return $"{prefix} {Declaration.Name}: {Declaration.Type}";
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
