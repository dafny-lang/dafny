using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class FieldSymbol(ILegacySymbol? scope, Field field) : MemberSymbol(scope, field), ILocalizableSymbol {
    public Field Declaration { get; } = field;
    public INode Node => Declaration;

    public string GetDetailText(DafnyOptions options, CancellationToken cancellationToken) {
      var prefix = Declaration.IsMutable ? "var" : "const";
      return $"{prefix} {TypePrefix}{Declaration.Name}: {Declaration.Type}";
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
