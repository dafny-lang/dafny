using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny; 

public class AllOpaqueRevealStmtInserter : IRewriter {
  public AllOpaqueRevealStmtInserter(ErrorReporter reporter) : base(reporter) { }
  
  internal override void PostResolveIntermediate(ModuleDefinition moduleDefinition) {
    Contract.Requires(moduleDefinition != null);

    foreach (var decl in ModuleDefinition.AllCallables(moduleDefinition.TopLevelDecls)) {
      if (decl is Method method && decl.WhatKind != "lemma") {
        AddMethodReveals(method);
      }
      else if (decl is Function func) {
        AddFunctionReveals(func);
      }
    }
  }

  protected void AddMethodReveals(Method m) {
    Contract.Requires(m != null);

    var currentClass = m.EnclosingClass;

    foreach (var iCallable in currentClass.EnclosingModuleDefinition.CallGraph.FindVertex(m).Successors) {
      var callable = iCallable.N;

      if (callable is Function func && !func.IsOpaque) {
        m.Body.Body.Insert(0, BuildRevealStmt(callable, currentClass, m.Tok));
      }
    }
  }

  protected void AddFunctionReveals(Function f) {
    Contract.Requires(f != null);

    var currentClass = f.EnclosingClass;

    foreach (var iCallable in currentClass.EnclosingModuleDefinition.CallGraph.FindVertex(f).Successors) {
      var callable = iCallable.N;

      if (callable is Function func && !func.IsOpaque) {
        if (f.Body != null) {
          var orig_expr = f.Body;
          var new_expr = new StmtExpr(f.Tok, BuildRevealStmt(callable, currentClass, f.Tok), orig_expr);
          new_expr.Type = orig_expr.Type;
          f.Body = new_expr;
        }
      }
    }
  }

  private RevealStmt BuildRevealStmt(ICallable callable, TopLevelDecl currentClass, IToken tok) {
    var expressionList = new List<Expression>();
    expressionList.Add(new ApplySuffix(tok, null,
      new NameSegment(callable.Tok, callable.NameRelativeToModule, new List<Type>()),
      new List<ActualBinding>(), tok));

    var receiver = new StaticReceiverExpr(tok,
      UserDefinedType.FromTopLevelDecl(tok, currentClass, currentClass.TypeArgs),
      (TopLevelDeclWithMembers)currentClass, true);

    var callable_name = "reveal_" + callable.NameRelativeToModule;
    var member = ((TopLevelDeclWithMembers)currentClass).Members.Find(decl => decl.Name == callable_name);

    var rr = new MemberSelectExpr(callable.Tok, receiver, callable_name);
    rr.Type = new UserDefinedType(tok, "_default", new List<Type>());;
    rr.Member = member;
    rr.TypeApplication_JustMember = new List<Type>();
    rr.TypeApplication_AtEnclosingClass = new List<Type>();

    var call = new CallStmt(callable.RangeToken, new List<Expression>(), rr, new List<ActualBinding>(),
      callable.Tok);
    call.Bindings.AcceptArgumentExpressionsAsExactParameterList(new List<Expression>());

    var revealStmt = new RevealStmt(callable.RangeToken, expressionList);
    revealStmt.ResolvedStatements.Add(call);

    return revealStmt;
  }
}