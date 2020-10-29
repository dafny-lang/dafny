using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// Visitor responsible to generate the LSP symbol representation.
  /// </summary>
  public class LspSymbolGeneratingVisitor : ISymbolVisitor<DocumentSymbol> {
    private readonly SymbolTable _symbolTable;
    private readonly CancellationToken _cancellationToken;

    public LspSymbolGeneratingVisitor(SymbolTable symbolTable, CancellationToken cancellationToken) {
      _symbolTable = symbolTable;
      _cancellationToken = cancellationToken;
    }

    public DocumentSymbol Visit(ISymbol symbol) {
      _cancellationToken.ThrowIfCancellationRequested();
      return symbol.Accept(this);
    }

    public DocumentSymbol Visit(CompilationUnit compilationUnit) {
      throw new System.NotImplementedException("cannot create a document symbol for the compilation unit");
    }

    public DocumentSymbol Visit(ModuleSymbol moduleSymbol) {
      _cancellationToken.ThrowIfCancellationRequested();
      return WithLocation(
        moduleSymbol,
        new DocumentSymbol {
          Name = moduleSymbol.Identifier,
          Kind = SymbolKind.Module,
          Detail = moduleSymbol.GetDetailText(_cancellationToken),
          Children = moduleSymbol.Children.Select(child => child.Accept(this)).ToArray()
        }
      );
    }

    public DocumentSymbol Visit(ClassSymbol classSymbol) {
      _cancellationToken.ThrowIfCancellationRequested();
      return WithLocation(
        classSymbol,
        new DocumentSymbol {
          Name = classSymbol.Identifier,
          Kind = SymbolKind.Class,
          Detail = classSymbol.GetDetailText(_cancellationToken),
          Children = classSymbol.Children.Select(child => child.Accept(this)).ToArray()
        }
      );
    }

    public DocumentSymbol Visit(FieldSymbol fieldSymbol) {
      _cancellationToken.ThrowIfCancellationRequested();
      return WithLocation(
        fieldSymbol,
        new DocumentSymbol {
          Name = fieldSymbol.Identifier,
          Kind = SymbolKind.Field,
          Detail = fieldSymbol.GetDetailText(_cancellationToken)
        }
      );
    }

    public DocumentSymbol Visit(FunctionSymbol functionSymbol) {
      _cancellationToken.ThrowIfCancellationRequested();
      return WithLocation(
        functionSymbol,
        new DocumentSymbol {
          Name = functionSymbol.Identifier,
          Kind = SymbolKind.Function,
          Detail = functionSymbol.GetDetailText(_cancellationToken),
          Children = functionSymbol.Children.Select(child => child.Accept(this)).ToArray()
        }
      );
    }

    public DocumentSymbol Visit(MethodSymbol methodSymbol) {
      _cancellationToken.ThrowIfCancellationRequested();
      return WithLocation(
        methodSymbol,
        new DocumentSymbol {
          Name = methodSymbol.Identifier,
          Kind = SymbolKind.Method,
          Detail = methodSymbol.GetDetailText(_cancellationToken),
          Children = methodSymbol.Children.Select(child => child.Accept(this)).ToArray()
        }
      );
    }

    public DocumentSymbol Visit(VariableSymbol variableSymbol) {
      _cancellationToken.ThrowIfCancellationRequested();
      return WithLocation(
        variableSymbol,
        new DocumentSymbol {
          Name = variableSymbol.Identifier,
          Kind = SymbolKind.Variable,
          Detail = variableSymbol.GetDetailText(_cancellationToken)
        }
      );
    }

    private DocumentSymbol WithLocation(ISymbol symbol, DocumentSymbol documentSymbol) {
      if(_symbolTable.TryGetLocationOf(symbol, out var location)) {
        documentSymbol.Range = location.Declaration;
        documentSymbol.SelectionRange = location.Identifier;
      }
      return documentSymbol;
    }
  }
}
