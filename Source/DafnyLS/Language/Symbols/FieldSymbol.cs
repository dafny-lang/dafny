using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  internal class FieldSymbol : Symbol, ILocalizableSymbol {
    public Field Declaration { get; }
    public object Node => Declaration;

    public FieldSymbol(ISymbol? scope, Field field) : base(scope, field.Name) {
      Declaration = field;
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"{Declaration.Name} : {Declaration.Type}";
    }

    public Range GetHoverRange() {
      return Declaration.tok.GetLspRange();
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
