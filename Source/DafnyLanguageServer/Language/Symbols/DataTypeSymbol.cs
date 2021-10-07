namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class DataTypeSymbol : TypeWithMembersSymbolBase<DatatypeDecl> {
    public DataTypeSymbol(ISymbol? scope, DatatypeDecl dataTypeDeclaration) : base(scope, dataTypeDeclaration) { }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
