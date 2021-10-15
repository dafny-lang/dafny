using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using AstElement = System.Object;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class DafnyLangTypeResolver {
    private readonly IDictionary<AstElement, ILocalizableSymbol> declarations;

    public DafnyLangTypeResolver(IDictionary<AstElement, ILocalizableSymbol> declarations) {
      this.declarations = declarations;
    }

    public bool TryGetTypeSymbol(Expression expression, [NotNullWhen(true)] out ISymbol? typeSymbol) {
      return TryGetTypeSymbol(expression.Type, out typeSymbol);
    }

    public bool TryGetTypeSymbol(Type type, [NotNullWhen(true)] out ISymbol? typeSymbol) {
      typeSymbol = type switch {
        UserDefinedType userDefinedType => GetTypeSymbol(userDefinedType),
        _ => null
      };
      return typeSymbol != null;
    }

    private ISymbol? GetTypeSymbol(UserDefinedType userDefinedType) {
      return userDefinedType.ResolvedClass switch {
        NonNullTypeDecl nonNullTypeDeclaration => GetSymbolByDeclaration(nonNullTypeDeclaration.Class),
        IndDatatypeDecl dataTypeDeclaration => GetSymbolByDeclaration(dataTypeDeclaration),
        _ => null
      };
    }

    private ISymbol? GetSymbolByDeclaration(AstElement node) {
      if (declarations.TryGetValue(node, out var symbol)) {
        return symbol;
      }
      return null;
    }
  }
}
