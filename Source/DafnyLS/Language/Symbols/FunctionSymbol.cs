using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  internal class FunctionSymbol : Symbol, ILocalizableSymbol {
    public Function Declaration { get; }
    public object Node => Declaration;

    public ISet<ISymbol> Parameters { get; } = new HashSet<ISymbol>();

    public override IEnumerable<ISymbol> Children => Parameters;

    public FunctionSymbol(ISymbol? scope, Function function) : base(scope, function.Name) {
      Declaration = function;
    }

    public DocumentSymbol AsLspSymbol(CancellationToken cancellationToken) {
      return new DocumentSymbol {
        Name = Declaration.Name,
        Kind = SymbolKind.Method,
        Range = new Range(Declaration.tok.GetLspPosition(), Declaration.BodyEndTok.GetLspPosition()),
        SelectionRange = GetHoverRange(),
        Detail = GetDetailText(cancellationToken),
        Children = Parameters.WithCancellation(cancellationToken).OfType<ILocalizableSymbol>().Select(child => child.AsLspSymbol(cancellationToken)).ToArray()
      };
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"function {Declaration.Name}({Declaration.Formals.AsCommaSeperatedText()}) : {Declaration.ResultType.AsText()}";
    }

    public Range GetHoverRange() {
      return Declaration.tok.GetLspRange();
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}