using Microsoft.Dafny;
using Microsoft.Extensions.Logging;
using System;
using System.IO;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// This visitor is the first pass when resolving the symbols of a given document. It visits
  /// all available declarations inside the document and stores them within the symbol table.
  /// </summary>
  internal class SymbolDeclarationResolvingVisitor : SyntaxTreeVisitor {
    private readonly ILogger _logger;

    private SymbolTable _currentTable;

    public SymbolDeclarationResolvingVisitor(ILogger logger, SymbolTable rootTable) {
      _logger = logger;
      _currentTable = rootTable;
    }

    public override void VisitUnknown(object node, Microsoft.Boogie.IToken token) {
      _logger.LogWarning("encountered unknown syntax node of type {} in {}@({},{})", node.GetType(), Path.GetFileName(token.filename), token.line, token.col);
    }

    public override void Visit(Method method) {
      _currentTable.Register(new MethodSymbol(method));
      ScopeSymbolTable(() => base.Visit(method));
    }

    public override void Visit(Function function) {
      _currentTable.Register(new FunctionSymbol(function));
      ScopeSymbolTable(() => base.Visit(function));
    }

    private void ScopeSymbolTable(Action inner) {
      _currentTable = _currentTable.NewChild();
      inner();
      // The field _currentTable is never null. Therefore, the parent of the table created at the beginning of this
      // method may never be null and the possible null-dereference can be safely discarded.
      _currentTable = _currentTable.Parent!;
    }

    public override void Visit(Formal formal) {
      _currentTable.Register(new VariableSymbol(formal));
    }

    public override void Visit(LocalVariable localVariable) {
      _currentTable.Register(new VariableSymbol(localVariable));
      base.Visit(localVariable);
    }
  }
}
