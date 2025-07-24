namespace Microsoft.Dafny;

class InvariantVisitor(ModuleResolver resolver) : ASTVisitor<InvariantVisitor.InvariantVisitorContext> {
  internal record InvariantVisitorContext(IASTVisitorContext AstVisitorContext) : IASTVisitorContext {
    ModuleDefinition IASTVisitorContext.EnclosingModule => AstVisitorContext.EnclosingModule;
  }

  public override InvariantVisitorContext GetContext(IASTVisitorContext astVisitorContext, bool inFunctionPostcondition) {
    return new InvariantVisitorContext(astVisitorContext);
  }

  protected override bool VisitOneExpression(Expression expr, InvariantVisitorContext context) {
    if (context.AstVisitorContext is Invariant { EnclosingClass: TopLevelDeclWithMembers enclosingDecl }) {
      if (expr is MemberSelectExpr { Member: var member } && enclosingDecl.InheritedMembers.Contains(member)) {
        resolver.reporter.Error(MessageSource.Resolver, expr.Origin,
          $"field '{member.Name}' of supertype trait '{member.EnclosingClass.Name}' cannot be referenced in invariant of '{enclosingDecl.Name}'");
      }
    }
    return true;
  }
}