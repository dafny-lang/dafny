using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using AstElement = System.Object;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class DafnyLangTypeResolver {
    private readonly IDictionary<AstElement, ILocalizableSymbol> declarations;

    public DafnyLangTypeResolver(IDictionary<AstElement, ILocalizableSymbol> declarations) {
      this.declarations = declarations;
    }

    public bool TryGetTypeSymbol(Expression expression, [NotNullWhen(true)] out ILegacySymbol? typeSymbol) {
      return TryGetTypeSymbol(expression.Type, out typeSymbol);
    }

    public bool TryGetTypeSymbol(Type type, [NotNullWhen(true)] out ILegacySymbol? typeSymbol) {
      typeSymbol = type switch {
        UserDefinedType userDefinedType => GetTypeSymbol(userDefinedType),
        _ => null
      };
      return typeSymbol != null;
    }

    private ILegacySymbol? GetTypeSymbol(UserDefinedType userDefinedType) {
      return userDefinedType.ResolvedClass switch {
        NonNullTypeDecl nonNullTypeDeclaration => GetSymbolByDeclaration(nonNullTypeDeclaration.Class),
        IndDatatypeDecl dataTypeDeclaration => GetSymbolByDeclaration(dataTypeDeclaration),
        TypeSynonymDecl typeSynonymDeclaration => GetTypeSynonymSymbol(userDefinedType, typeSynonymDeclaration),
        _ => null
      };
    }

    private ILegacySymbol? GetTypeSynonymSymbol(UserDefinedType userDefinedType, TypeSynonymDecl typeSynonymDeclaration) {
      ILegacySymbol? symbol = null;
      // It would probably be less brittle to reuse Dafny's type resolution logic here
      var typeSubstitutions = typeSynonymDeclaration.TypeArgs
        .Zip(userDefinedType.TypeArgs)
        .ToDictionary(pair => pair.First, pair => pair.Second);
      var rhsAfterSubstitution = typeSynonymDeclaration.Rhs.Subst(typeSubstitutions);
      TryGetTypeSymbol(rhsAfterSubstitution, out symbol);
      return symbol;
    }

    private ILegacySymbol? GetSymbolByDeclaration(AstElement node) {
      if (declarations.TryGetValue(node, out var symbol)) {
        return symbol;
      }
      return null;
    }
  }
}
