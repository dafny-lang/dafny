namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class ClassSymbol(ILegacySymbol? scope, TopLevelDeclWithMembers classDeclaration)
    : TypeWithMembersSymbolBase<TopLevelDeclWithMembers>(scope, classDeclaration) {
    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
