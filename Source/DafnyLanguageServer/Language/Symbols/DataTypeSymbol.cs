namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class DataTypeSymbol(ILegacySymbol? scope, DatatypeDecl dataTypeDeclaration)
    : TypeWithMembersSymbolBase<DatatypeDecl>(scope, dataTypeDeclaration) {
    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
