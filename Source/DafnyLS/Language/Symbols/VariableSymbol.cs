using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  internal class VariableSymbol : Symbol, ILocalizableSymbol {
    public IVariable Declaration { get; }
    public object Node => Declaration;

    public VariableSymbol(ISymbol? scope, IVariable variable) : base(scope, variable.Name) {
      Declaration = variable;
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"{Declaration.Name} : {Declaration.Type}";
    }

    public Range GetHoverRange() {
      return Declaration.Tok.GetLspRange();
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
