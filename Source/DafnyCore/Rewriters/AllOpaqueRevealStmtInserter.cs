using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny; 

public class AllOpaqueRevealStmtInserter : IRewriter {
  public AllOpaqueRevealStmtInserter(ErrorReporter reporter) : base(reporter) { }
  
  internal override void PostResolveIntermediate(ModuleDefinition moduleDefinition) {
    Contract.Requires(moduleDefinition != null);

    // foreach (var decl in ModuleDefinition.AllCallables(moduleDefinition.TopLevelDecls)) {
    foreach (var decl in moduleDefinition.TopLevelDecls) {
      if (decl is TopLevelDeclWithMembers cl) {
        foreach (var member in cl.Members.Where(member => member is ICallable and not ConstantField)) {
          var mem = (ICallable)member;
          if (member is Function { ByMethodDecl: { } } f) {
            mem = f.ByMethodDecl;
          }
          
          if (mem is Method { Body: not null } method) {
            AddMethodReveals(method);
          }
          else if (mem is Function { Body: not null } func) {
            AddFunctionReveals(func);
          }
        }
      }
    }
  }

  private void AddMethodReveals(Method m) {
    Contract.Requires(m != null);

    var currentClass = m.EnclosingClass;

    var vertex = currentClass.EnclosingModuleDefinition.CallGraph.FindVertex(m);

    if (vertex is null) {
      return;
    }  //vertex can be null if m is a Test method.
    
    var visited = new HashSet<Graph<ICallable>.Vertex>();
    var queue = new Queue<Graph<ICallable>.Vertex>();

    foreach (var callable in vertex.Successors) {
      queue.Enqueue(callable);
    }

    while (queue.Any()) {
      var newVertex = queue.Dequeue();
      if (!visited.Contains(newVertex)) {
        foreach (var vertex0 in newVertex.Successors) {
          queue.Enqueue(vertex0);
        }

        var callable = newVertex.N;
        
        if (callable is Function { IsOpaque: false } func) {
          var revealStmt = BuildRevealStmt(func, currentClass, m.Tok);

          if (revealStmt is not null) {
            m.Body.Body.Insert(0, revealStmt);
          }
        }

        visited.Add(newVertex);
      }
    }
    
    // foreach (var callable in vertex.Successors.Select(iCallable => iCallable.N))
    // {
    //   if (callable is Function { IsOpaque: false } func) {
    //     var revealStmt = BuildRevealStmt(func, currentClass, m.Tok);
    //
    //     if (revealStmt is not null) {
    //       m.Body.Body.Insert(0, revealStmt);
    //     }
    //   }
    // }
  }

  private static void AddFunctionReveals(Function f) {
    Contract.Requires(f != null);

    var currentClass = f.EnclosingClass;
    var vertex = currentClass.EnclosingModuleDefinition.CallGraph.FindVertex(f);

    if (vertex is null) {
      return;
    }  //vertex can be null if m is a Test method.

    var visited = new HashSet<Graph<ICallable>.Vertex>();
    var queue = new Queue<Graph<ICallable>.Vertex>();

    foreach (var callable in vertex.Successors) {
      queue.Enqueue(callable);
    }

    while (queue.Any()) {
      var newVertex = queue.Dequeue();
      if (!visited.Contains(newVertex)) {
        foreach (var vertex0 in newVertex.Successors) {
          queue.Enqueue(vertex0);
        }

        var callable = newVertex.N;
        
        if (callable is Function { IsOpaque: false } func) {
          var origExpr = f.Body;
          var revealStmt = BuildRevealStmt(func, currentClass, f.Tok);

          if (revealStmt is not null) {
            var newExpr = new StmtExpr(f.Tok, BuildRevealStmt(func, currentClass, f.Tok), origExpr);
            newExpr.Type = origExpr.Type;
            f.Body = newExpr;
          }
        }

        visited.Add(newVertex);
      }
    }

    // foreach (var callable in vertex.Successors.Select(iCallable => iCallable.N)) {
    //   
    //   if (callable is Function { IsOpaque: false } func) {
    //     var origExpr = f.Body;
    //     var revealStmt = BuildRevealStmt(func, currentClass, f.Tok);
    //
    //     if (revealStmt is not null) {
    //       var newExpr = new StmtExpr(f.Tok, BuildRevealStmt(func, currentClass, f.Tok), origExpr);
    //       newExpr.Type = origExpr.Type;
    //       f.Body = newExpr;
    //     }
    //   }
    // }
  }

  private static RevealStmt BuildRevealStmt(Function callable, TopLevelDecl currentClass, IToken tok) {
    var expressionList = new List<Expression> {
      new ApplySuffix(tok, null,
        new NameSegment(callable.Tok, callable.Name, new List<Type>()),
        new List<ActualBinding>(), tok)
    };

    var callableClass = ((TopLevelDeclWithMembers)callable.EnclosingClass);

    // Original:
    // var receiver = new StaticReceiverExpr(tok,
    //   UserDefinedType.FromTopLevelDecl(tok, currentClass, currentClass.TypeArgs),
    //   (TopLevelDeclWithMembers)currentClass, true);
    
    // var ri = (Resolver_IdentifierExpr)lhs;
    // // ----- 3. Look up name in type
    // // expand any synonyms
    
    
    // var receiver = new StaticReceiverExpr(tok, new UserDefinedType(), 
    //   UserDefinedType.FromTopLevelDecl(tok, callableClass, callableClass.TypeArgs.ConvertAll(obj => new UserDefinedType(tok, "_tuple#0", new List<Type>()) )), callableClass, true);

    var callableName = "reveal_" + callable.Name;
    // var name = resolutionContext.InReveal ? "reveal_" + expr.SuffixName : expr.SuffixName
    var member = callableClass.Members.Find(decl => decl.Name == callableName);
    
    
    var receiver = new StaticReceiverExpr(tok, new UserDefinedType(tok, callableName, callableClass, callableClass.TypeArgs.ConvertAll(obj => (Type) Type.Int) ), callableClass, true);

    if (member is null) {
      return null;
    }

    var ty = new UserDefinedType(tok, callableName, callableClass, callableClass.TypeArgs.ConvertAll(obj =>
      ((Type)(new UserDefinedType(tok, "_tuple#0", new List<Type>())))));
    
    // var receiver = new StaticReceiverExpr(tok, (UserDefinedType)ty.NormalizeExpand(), callableClass, false);
    // receiver.ContainerExpression = expr.Lhs;
    
    
    callableName = ((ICallable)member).NameRelativeToModule;
    var rr = new MemberSelectExpr(callable.Tok, receiver, callableName);
    rr.Type = new UserDefinedType(tok, "_default", new List<Type>());;
    rr.Member = member;
    rr.TypeApplication_JustMember = new List<Type>();
    rr.TypeApplication_AtEnclosingClass = new List<Type>();

    var call = new CallStmt(callable.RangeToken, new List<Expression>(), rr, new List<ActualBinding>(),
      callable.Tok);
    call.Bindings.AcceptArgumentExpressionsAsExactParameterList(new List<Expression>());

    var revealStmt = new RevealStmt(callable.RangeToken, expressionList);
    revealStmt.ResolvedStatements.Add(call);
    revealStmt.IsGhost = true;
    // revealStmt.Attributes = new Attributes("", new List<Expression>(), null);

    return revealStmt;
  }
}