using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  internal class ClassSymbol : Symbol, ILocalizableSymbol {
    private readonly ClassDecl _node;

    public IList<Symbol> Members { get; } = new List<Symbol>();

    public override IEnumerable<Symbol> Children => Members;

    public ClassSymbol(Symbol? scope, ClassDecl classDeclaration) : base(scope, classDeclaration.Name) {
      _node = classDeclaration;
    }

    public DocumentSymbol AsLspSymbol(CancellationToken cancellationToken) {
      return new DocumentSymbol {
        Name = _node.Name,
        Kind = SymbolKind.Class,
        Range = new Range(_node.tok.GetLspPosition(), _node.BodyEndTok.GetLspPosition()),
        SelectionRange = GetHoverRange(),
        Detail = GetDetailText(cancellationToken),
        Children = Members.WithCancellation(cancellationToken).OfType<ILocalizableSymbol>().Select(child => child.AsLspSymbol(cancellationToken)).ToArray()
      };
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"class {_node.Name}";
    }

    public Range GetHoverRange() {
      return _node.tok.GetLspRange();
    }
  }
}
