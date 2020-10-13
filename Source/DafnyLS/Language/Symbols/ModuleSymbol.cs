using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  internal class ModuleSymbol : Symbol, ILocalizableSymbol {
    private readonly ModuleDefinition _node;

    public ISet<Symbol> Declarations { get; } = new HashSet<Symbol>();

    public ModuleSymbol(Symbol? scope, ModuleDefinition moduleDefinition) : base(scope, moduleDefinition.Name) {
      _node = moduleDefinition;
    }

    public DocumentSymbol AsLspSymbol(CancellationToken cancellationToken) {
      return new DocumentSymbol {
        Name = _node.Name,
        Kind = SymbolKind.Module,
        Range = new Range(_node.tok.GetLspPosition(), _node.BodyEndTok.GetLspPosition()),
        SelectionRange = GetHoverRange(),
        Detail = GetDetailText(cancellationToken),
        Children = Declarations.WithCancellation(cancellationToken).OfType<ILocalizableSymbol>().Select(child => child.AsLspSymbol(cancellationToken)).ToArray()
      };
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"module {_node.Name}";
    }

    public Range GetHoverRange() {
      return _node.tok.GetLspRange();
    }

    public override IEnumerable<Symbol> GetAllDescendantsAndSelf() {
      yield return this;
      foreach(var declaration in Declarations) {
        foreach(var descendant in declaration.GetAllDescendantsAndSelf()) {
          yield return descendant;
        }
      }
    }
  }
}
