using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class VariableSymbol(ILegacySymbol? scope, IVariable variable)
    : Symbol(scope, variable.Name), ILocalizableSymbol {
    public IVariable Declaration { get; } = variable;
    public INode Node => Declaration;

    public string GetDetailText(DafnyOptions options, CancellationToken cancellationToken) {
      return Declaration.AsText();
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
