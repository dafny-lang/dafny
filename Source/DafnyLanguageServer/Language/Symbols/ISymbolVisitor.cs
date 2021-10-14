namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// Visitor to traverse the symbol hierarchy.
  /// </summary>
  /// <typeparam name="TResult">The return value of the visit methods.</typeparam>
  public interface ISymbolVisitor<TResult> {
    TResult Visit(ISymbol symbol);

    TResult Visit(CompilationUnit compilationUnit);

    TResult Visit(ModuleSymbol moduleSymbol);

    TResult Visit(ClassSymbol classSymbol);

    TResult Visit(DataTypeSymbol dataTypeSymbol);

    TResult Visit(ValueTypeSymbol valueTypeSymbol);

    TResult Visit(FieldSymbol fieldSymbol);

    TResult Visit(FunctionSymbol functionSymbol);

    TResult Visit(MethodSymbol methodSymbol);

    TResult Visit(VariableSymbol variableSymbol);

    TResult Visit(ScopeSymbol scopeSymbol);
  }
}
