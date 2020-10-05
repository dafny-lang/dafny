using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  internal class ClassSymbol : ISymbol {
    private readonly ClassDecl _node;

    public ClassSymbol(ClassDecl classDeclaration) {
      _node = classDeclaration;
    }

    public DocumentSymbol AsLspSymbol(CancellationToken cancellationToken) {
      return new DocumentSymbol {
        Name = _node.Name,
        Kind = SymbolKind.Class,
        Range = new Range(_node.tok.GetLspPosition(), _node.BodyEndTok.GetLspPosition()),
        SelectionRange = _node.tok.GetLspRange(),
        Detail = GetDetailText(cancellationToken)
        // TODO children should probably resolved with the visitor.
      };
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"class {_node.Name}";
    }
  }
}
