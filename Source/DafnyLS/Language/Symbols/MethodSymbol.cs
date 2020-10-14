using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  internal class MethodSymbol : Symbol, ILocalizableSymbol {
    private readonly Method _node;

    public object Node => _node;

    public ISet<ISymbol> Parameters { get; } = new HashSet<ISymbol>();
    public ISet<ISymbol> Returns { get; } = new HashSet<ISymbol>();

    public override IEnumerable<ISymbol> Children => Parameters.Concat(Returns);

    public MethodSymbol(ISymbol? scope, Method method) : base(scope, method.Name) {
      _node = method;
    }

    public DocumentSymbol AsLspSymbol(CancellationToken cancellationToken) {
      return new DocumentSymbol {
        Name = _node.Name,
        Kind = SymbolKind.Method,
        Range = new Range(_node.tok.GetLspPosition(), _node.BodyEndTok.GetLspPosition()),
        SelectionRange = GetHoverRange(),
        Detail = GetDetailText(cancellationToken),
        Children = Parameters.Concat(Returns).WithCancellation(cancellationToken).OfType<ILocalizableSymbol>().Select(child => child.AsLspSymbol(cancellationToken)).ToArray()
      };
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"method {_node.Name}({_node.Ins.AsCommaSeperatedText()}) : ({_node.Outs.AsCommaSeperatedText()})";
    }

    public Range GetHoverRange() {
      return _node.tok.GetLspRange();
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
