using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Linq;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// Visitor responsible to generate the LSP symbol representation.
  /// </summary>
  public class LspSymbolGeneratingVisitor : ISymbolVisitor<DocumentSymbol> {
    private readonly CancellationToken _cancellationToken;

    public LspSymbolGeneratingVisitor(CancellationToken cancellationToken) {
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
      return new DocumentSymbol {
        Name = moduleSymbol.Identifier,
        Kind = SymbolKind.Module,
        Range = new Range(moduleSymbol.Declaration.tok.GetLspPosition(), moduleSymbol.Declaration.BodyEndTok.GetLspPosition()),
        SelectionRange = moduleSymbol.GetHoverRange(),
        Detail = moduleSymbol.GetDetailText(_cancellationToken),
        Children = moduleSymbol.Children.Select(child => child.Accept(this)).ToArray()
      };
    }

    public DocumentSymbol Visit(ClassSymbol classSymbol) {
      _cancellationToken.ThrowIfCancellationRequested();
      return new DocumentSymbol {
        Name = classSymbol.Identifier,
        Kind = SymbolKind.Class,
        Range = new Range(classSymbol.Declaration.tok.GetLspPosition(), classSymbol.Declaration.BodyEndTok.GetLspPosition()),
        SelectionRange = classSymbol.GetHoverRange(),
        Detail = classSymbol.GetDetailText(_cancellationToken),
        Children = classSymbol.Children.Select(child => child.Accept(this)).ToArray()
      };
    }

    public DocumentSymbol Visit(FieldSymbol fieldSymbol) {
      _cancellationToken.ThrowIfCancellationRequested();
      return new DocumentSymbol {
        Name = fieldSymbol.Identifier,
        Kind = SymbolKind.Field,
        Range = fieldSymbol.Declaration.tok.GetLspRange(),
        SelectionRange = fieldSymbol.GetHoverRange(),
        Detail = fieldSymbol.GetDetailText(_cancellationToken)
      };
    }

    public DocumentSymbol Visit(FunctionSymbol functionSymbol) {
      _cancellationToken.ThrowIfCancellationRequested();
      return new DocumentSymbol {
        Name = functionSymbol.Identifier,
        Kind = SymbolKind.Function,
        Range = new Range(functionSymbol.Declaration.tok.GetLspPosition(), functionSymbol.Declaration.BodyEndTok.GetLspPosition()),
        SelectionRange = functionSymbol.GetHoverRange(),
        Detail = functionSymbol.GetDetailText(_cancellationToken),
        Children = functionSymbol.Children.Select(child => child.Accept(this)).ToArray()
      };
    }

    public DocumentSymbol Visit(MethodSymbol methodSymbol) {
      _cancellationToken.ThrowIfCancellationRequested();
      return new DocumentSymbol {
        Name = methodSymbol.Identifier,
        Kind = SymbolKind.Method,
        Range = new Range(methodSymbol.Declaration.tok.GetLspPosition(), methodSymbol.Declaration.BodyEndTok.GetLspPosition()),
        SelectionRange = methodSymbol.GetHoverRange(),
        Detail = methodSymbol.GetDetailText(_cancellationToken),
        Children = methodSymbol.Children.Select(child => child.Accept(this)).ToArray()
      };
    }

    public DocumentSymbol Visit(VariableSymbol variableSymbol) {
      _cancellationToken.ThrowIfCancellationRequested();
      return new DocumentSymbol {
        Name = variableSymbol.Identifier,
        Kind = SymbolKind.Variable,
        Range = variableSymbol.Declaration.Tok.GetLspRange(),
        SelectionRange = variableSymbol.GetHoverRange(),
        Detail = variableSymbol.GetDetailText(_cancellationToken)
      };
    }
  }
}
