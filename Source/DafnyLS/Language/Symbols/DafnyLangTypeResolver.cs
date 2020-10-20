using Microsoft.Dafny;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using AstElement = System.Object;

namespace DafnyLS.Language.Symbols {
  public class DafnyLangTypeResolver {
    private readonly IDictionary<AstElement, ILocalizableSymbol> _declarations;

    public DafnyLangTypeResolver(IDictionary<AstElement, ILocalizableSymbol> declarations) {
      _declarations = declarations;
    }

    public bool TryGetTypeSymbol(Expression expression, [NotNullWhen(true)] out ISymbol? typeSymbol) {
      typeSymbol = expression.Type switch {
        UserDefinedType userDefinedType => GetTypeSymbol(userDefinedType),
        _ => null
      };
      return typeSymbol != null;
    }

    private ISymbol? GetTypeSymbol(UserDefinedType userDefinedType) {
      return userDefinedType.ResolvedClass switch {
        NonNullTypeDecl nonNullTypeDeclaration => GetSymbolByDeclaration(nonNullTypeDeclaration.Class),
        _ => null
      };
    }

    private ISymbol? GetSymbolByDeclaration(AstElement node) {
      if(_declarations.TryGetValue(node, out var symbol)) {
        return symbol;
      }
      return null;
    }
  }
}
