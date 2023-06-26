using System;
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
      } else if (decl is SubsetTypeDecl { Witness: not null } expr) {
        var functionCalls = expr.Constraint.SubExpressions.ToList().Concat(expr.Witness.SubExpressions.ToList());
        foreach (var expression in functionCalls) {
          if (expression is FunctionCallExpr funcExpr) {
            var func = funcExpr.Function;
            var revealStmt = BuildRevealStmt(func, expr.Witness.Tok);

            if (revealStmt is not null) {
              var newExpr = new StmtExpr(expr.Witness.Tok, revealStmt, expr.Witness) {
                Type = expr.Witness.Type
              };
              expr.Witness = newExpr;
            }
              
            using IEnumerator<Function> enumerator = GetEnumerator(func, func.EnclosingClass);
            while (enumerator.MoveNext()) {
              var newFunc = enumerator.Current;
      
              var origExpr = expr.Witness;
              var newRevealStmt = BuildRevealStmt(newFunc, expr.Witness.Tok);

              if (revealStmt is not null) {
                var newExpr = new StmtExpr(expr.Witness.Tok, newRevealStmt, origExpr) {
                  Type = origExpr.Type
                };
                expr.Witness = newExpr;
              }
            }
          }
        }
      } else {
        
      }
    }
  }
  
  internal class GraphTraversalVertex {
    public readonly Graph<ICallable>.Vertex vertex;
    public readonly bool local;

    public GraphTraversalVertex(Graph<ICallable>.Vertex vertex, bool local) {
      this.vertex = vertex;
      this.local = local;
    }

    public override bool Equals(object obj)
    {
      GraphTraversalVertex other = obj as GraphTraversalVertex;
      return other.vertex == vertex && other.local == local;
    }

    public override int GetHashCode()
    {
      return HashCode.Combine(vertex, local);
    }

  }

  private void AddMethodReveals(Method m) {
    Contract.Requires(m != null);

    var currentClass = m.EnclosingClass;

    using IEnumerator<Function> enumerator = GetEnumerator(m, currentClass);
    while (enumerator.MoveNext())
    {
      var func = enumerator.Current;
      var revealStmt = BuildRevealStmt(func, m.Tok);

      if (revealStmt is not null) {
        m.Body.Body.Insert(0, revealStmt);
      }
    }
  }
  
  
  private void AddFunctionReveals(Function f) {
    Contract.Requires(f != null);

    var currentClass = f.EnclosingClass;

    using IEnumerator<Function> enumerator = GetEnumerator(f, currentClass);
    while (enumerator.MoveNext()) {
      var func = enumerator.Current;
      
      var origExpr = f.Body;
      var revealStmt = BuildRevealStmt(func, f.Tok);

      if (revealStmt is not null) {
        var newExpr = new StmtExpr(f.Tok, revealStmt, origExpr) {
          Type = origExpr.Type
        };
        f.Body = newExpr;
      }
    }
  }
  
  private IEnumerator<Function> GetEnumerator(ICallable m, TopLevelDecl currentClass) {
    var vertex = currentClass.EnclosingModuleDefinition.CallGraph.FindVertex(m);
    var interModuleVertex = currentClass.EnclosingModuleDefinition.InterModuleCallGraph.FindVertex(m);

    if (vertex is null) {
      yield break;
    }  //vertex can be null if m is a Test method.

    var visited = new HashSet<GraphTraversalVertex>();
    var queue = new Queue<GraphTraversalVertex>();

    foreach (var callable in vertex.Successors) {
      queue.Enqueue(new GraphTraversalVertex(callable, true));
    }

    if (interModuleVertex is not null) {
      foreach (var callable in interModuleVertex.Successors) {
        queue.Enqueue(new GraphTraversalVertex(callable, false));
      }
    }

    while (queue.Any()) {
      var newVertex = queue.Dequeue();
      if (!visited.Contains(newVertex)) {
        visited.Add(newVertex);
        
        Graph<ICallable>.Vertex origNewVertex;
        Graph<ICallable>.Vertex newInterModuleVertex;

        if (newVertex.local) {
          origNewVertex = newVertex.vertex;
          newInterModuleVertex = origNewVertex.N.EnclosingModule.InterModuleCallGraph.FindVertex(origNewVertex.N);
        } else {
          origNewVertex = newVertex.vertex.N.EnclosingModule.CallGraph.FindVertex(newVertex.vertex.N);
          
          if (origNewVertex is null) {
            continue;
          }
          newInterModuleVertex = origNewVertex.N.EnclosingModule.InterModuleCallGraph.FindVertex(origNewVertex.N);
        }
        
        foreach (var vertex0 in origNewVertex.Successors) {
          queue.Enqueue(new GraphTraversalVertex(vertex0, true));
        }

        if (newInterModuleVertex is not null) {
          foreach (var vertex0 in newInterModuleVertex.Successors) {
            queue.Enqueue(new GraphTraversalVertex(vertex0, false));
          }
        }

        var callable = origNewVertex.N;
        
        if (callable is Function { IsOpaque: false } func) {
          yield return func;
        }
      }
    }
  }

  private static RevealStmt BuildRevealStmt(Function callable, IToken tok) {
    var expressionList = new List<Expression> {
      new ApplySuffix(tok, null,
        new NameSegment(callable.Tok, callable.Name, new List<Type>()),
        new List<ActualBinding>(), tok)
    };

    var callableClass = ((TopLevelDeclWithMembers)callable.EnclosingClass);

    var callableName = "reveal_" + callable.Name;
    var member = callableClass.Members.Find(decl => decl.Name == callableName);
    
    
    var receiver = new StaticReceiverExpr(tok, new UserDefinedType(tok, callableName, callableClass, callableClass.TypeArgs.ConvertAll(obj => (Type) Type.Int) ), callableClass, true);

    if (member is null) {
      return null;
    }

    var ty = new UserDefinedType(tok, callableName, callableClass, callableClass.TypeArgs.ConvertAll(obj =>
      ((Type)(new UserDefinedType(tok, "_tuple#0", new List<Type>())))));

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

    return revealStmt;
  }
}


// ----------------


  // var vertex = currentClass.EnclosingModuleDefinition.CallGraph.FindVertex(m);
    // var interModuleVertex = currentClass.EnclosingModuleDefinition.InterModuleCallGraph.FindVertex(m);
    //
    // if (vertex is null) {
    //   return;
    // }  //vertex can be null if m is a Test method.
    //
    // var visited = new HashSet<GraphTraversalVertex>();
    // var queue = new Queue<GraphTraversalVertex>();
    //
    // foreach (var callable in vertex.Successors) {
    //   queue.Enqueue(new GraphTraversalVertex(callable, true));
    // }
    //
    // if (interModuleVertex is not null) {
    //   foreach (var callable in interModuleVertex.Successors) {
    //     queue.Enqueue(new GraphTraversalVertex(callable, false));
    //   }
    // }
    //
    // while (queue.Any()) {
    //   var newVertex = queue.Dequeue();
    //   if (!visited.Contains(newVertex)) {
    //     Graph<ICallable>.Vertex origNewVertex;
    //     Graph<ICallable>.Vertex newInterModuleVertex;
    //
    //     if (newVertex.local) {
    //       origNewVertex = newVertex.vertex;
    //       newInterModuleVertex = origNewVertex.N.EnclosingModule.InterModuleCallGraph.FindVertex(origNewVertex.N);
    //     } else {
    //       origNewVertex = newVertex.vertex.N.EnclosingModule.CallGraph.FindVertex(newVertex.vertex.N);
    //       
    //       if (origNewVertex is null) {
    //         continue;
    //       }
    //       newInterModuleVertex = origNewVertex.N.EnclosingModule.InterModuleCallGraph.FindVertex(origNewVertex.N);
    //     }
    //     
    //     foreach (var vertex0 in origNewVertex.Successors) {
    //       queue.Enqueue(new GraphTraversalVertex(vertex0, true));
    //     }
    //
    //     if (newInterModuleVertex is not null) {
    //       foreach (var vertex0 in newInterModuleVertex.Successors) {
    //         queue.Enqueue(new GraphTraversalVertex(vertex0, false));
    //       }
    //     }
    //
    //     var callable = origNewVertex.N;
    //     
    //     if (callable is Function { IsOpaque: false } func) {
    //       var revealStmt = BuildRevealStmt(func, currentClass, m.Tok);
    //
    //       if (revealStmt is not null) {
    //         m.Body.Body.Insert(0, revealStmt);
    //       }
    //     }
    //
    //     visited.Add(newVertex);
    //   }
    // }

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
    
    
    
    //----
    
        
    // var vertex = currentClass.EnclosingModuleDefinition.CallGraph.FindVertex(f);
    // var interModuleVertex = currentClass.EnclosingModuleDefinition.InterModuleCallGraph.FindVertex(f);
    //
    //
    // if (vertex is null) {
    //   return;
    // }  //vertex can be null if m is a Test method.
    //
    // var visited = new HashSet<GraphTraversalVertex>();
    // var queue = new Queue<GraphTraversalVertex>();
    //
    // foreach (var callable in vertex.Successors) {
    //   queue.Enqueue(new GraphTraversalVertex(callable, true));
    // }
    //
    // if (interModuleVertex is not null) {
    //   foreach (var callable in interModuleVertex.Successors) {
    //     queue.Enqueue(new GraphTraversalVertex(callable, false));
    //   }
    // }
    //
    // while (queue.Any()) {
    //   var newVertex = queue.Dequeue();
    //   if (!visited.Contains(newVertex)) {
    //     Graph<ICallable>.Vertex origNewVertex;
    //     Graph<ICallable>.Vertex newInterModuleVertex;
    //     
    //     if (newVertex.local) {
    //       origNewVertex = newVertex.vertex;
    //       newInterModuleVertex = origNewVertex.N.EnclosingModule.InterModuleCallGraph.FindVertex(origNewVertex.N);
    //     } else {
    //       origNewVertex = newVertex.vertex.N.EnclosingModule.CallGraph.FindVertex(newVertex.vertex.N);
    //
    //       if (origNewVertex is null) {
    //         continue;
    //       }
    //       newInterModuleVertex = origNewVertex.N.EnclosingModule.InterModuleCallGraph.FindVertex(origNewVertex.N);
    //     }
    //     
    //     foreach (var vertex0 in origNewVertex.Successors) {
    //       queue.Enqueue(new GraphTraversalVertex(vertex0, true));
    //     }
    //     
    //     if (newInterModuleVertex is not null) {
    //       foreach (var vertex0 in newInterModuleVertex.Successors) {
    //         queue.Enqueue(new GraphTraversalVertex(vertex0, false));
    //       }
    //     }
    //
    //     var callable = origNewVertex.N;
    //     
    //     if (callable is Function { IsOpaque: false } func) {
    //       var origExpr = f.Body;
    //       var revealStmt = BuildRevealStmt(func, currentClass, f.Tok);
    //
    //       if (revealStmt is not null) {
    //         var newExpr = new StmtExpr(f.Tok, BuildRevealStmt(func, currentClass, f.Tok), origExpr) {
    //           Type = origExpr.Type
    //         };
    //         f.Body = newExpr;
    //       }
    //
    //     }
    //
    //     visited.Add(newVertex);
    //   }
    // }

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