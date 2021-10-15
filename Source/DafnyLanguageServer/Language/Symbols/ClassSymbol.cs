namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class ClassSymbol : TypeWithMembersSymbolBase<ClassDecl> {
    public ClassSymbol(ISymbol? scope, ClassDecl classDeclaration) : base(scope, classDeclaration) { }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
