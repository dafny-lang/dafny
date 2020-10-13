using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  internal class MethodSymbol : Symbol, ILocalizableSymbol {
    private readonly Method _node;

    public ISet<Symbol> Parameters { get; } = new HashSet<Symbol>();
    public ISet<Symbol> Returns { get; } = new HashSet<Symbol>();

    public MethodSymbol(Symbol? scope, Method method) : base(scope, method.Name) {
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

    public override IEnumerable<Symbol> GetAllDescendantsAndSelf() {
      yield return this;
      foreach(var child in Parameters.Concat(Returns)) {
        foreach(var descendant in child.GetAllDescendantsAndSelf()) {
          yield return descendant;
        }
      }
    }
  }
}
