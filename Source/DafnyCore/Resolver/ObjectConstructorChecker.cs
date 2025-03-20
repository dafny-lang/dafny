//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

namespace Microsoft.Dafny;

class ObjectConstructorChecker : ASTVisitor<IASTVisitorContext> {
  private readonly ErrorReporter reporter;

  public ObjectConstructorChecker(ErrorReporter reporter) {
    this.reporter = reporter;
  }

  public override IASTVisitorContext GetContext(IASTVisitorContext astVisitorContext, bool inFunctionPostcondition) {
    return astVisitorContext;
  }

  protected override bool VisitOneStatement(Statement stmt, IASTVisitorContext context) {
    if (stmt is SingleAssignStmt { Rhs: AllocateClass rr } && (rr.Bindings == null || rr.InitCall.Method is not Constructor)) {
      // this is an AssignStmt that allocates one object and does not call a constructor
      var udt = (UserDefinedType)rr.Type.NormalizeExpand();
      var cl = (ClassLikeDecl)udt.ResolvedClass;
      if (!cl.IsObjectTrait && !udt.IsArrayType) {
        var classHasConstructor = cl is ClassDecl { HasConstructor: true };
        if (classHasConstructor || cl.EnclosingModuleDefinition != context.EnclosingModule) {
          reporter.Error(MessageSource.Resolver, stmt,
            $"when allocating an object of {(classHasConstructor ? "" : "imported ")}type '{cl.Name}', one of its constructor methods must be called");
        }
      }
    }
    return base.VisitOneStatement(stmt, context);
  }
}
