namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class ClassSymbol : TypeWithMembersSymbolBase<TopLevelDeclWithMembers> {
    public ClassSymbol(ISymbol? scope, TopLevelDeclWithMembers classDeclaration) : base(scope, classDeclaration) { }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
