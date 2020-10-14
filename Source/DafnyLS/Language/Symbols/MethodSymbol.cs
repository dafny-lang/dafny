using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  internal class MethodSymbol : Symbol, ILocalizableSymbol {
    public Method Declaration { get; }
    public object Node => Declaration;

    public ISet<ISymbol> Parameters { get; } = new HashSet<ISymbol>();
    public ISet<ISymbol> Returns { get; } = new HashSet<ISymbol>();

    public override IEnumerable<ISymbol> Children => Parameters.Concat(Returns);

    public MethodSymbol(ISymbol? scope, Method method) : base(scope, method.Name) {
      Declaration = method;
    }

    public DocumentSymbol AsLspSymbol(CancellationToken cancellationToken) {
      return new DocumentSymbol {
        Name = Declaration.Name,
        Kind = SymbolKind.Method,
        Range = new Range(Declaration.tok.GetLspPosition(), Declaration.BodyEndTok.GetLspPosition()),
        SelectionRange = GetHoverRange(),
        Detail = GetDetailText(cancellationToken),
        Children = Parameters.Concat(Returns).WithCancellation(cancellationToken).OfType<ILocalizableSymbol>().Select(child => child.AsLspSymbol(cancellationToken)).ToArray()
      };
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"method {Declaration.Name}({Declaration.Ins.AsCommaSeperatedText()}) : ({Declaration.Outs.AsCommaSeperatedText()})";
    }

    public Range GetHoverRange() {
      return Declaration.tok.GetLspRange();
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
