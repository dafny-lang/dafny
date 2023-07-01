using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Linq.Expressions;
using Microsoft.Boogie;

namespace Microsoft.Dafny; 

public class AllOpaqueRevealStmtInserter : IRewriter {
  public AllOpaqueRevealStmtInserter(ErrorReporter reporter) : base(reporter) { }
  
  internal override void PostResolveIntermediate(ModuleDefinition moduleDefinition) {
    Contract.Requires(moduleDefinition != null);

    // foreach (var decl in ModuleDefinition.AllCallables(moduleDefinition.TopLevelDecls)) {
    foreach (var decl in moduleDefinition.TopLevelDecls) {
      if (decl is TopLevelDeclWithMembers cl) {
        foreach (var member in cl.Members) { //.Where(member => member is ICallable and not ConstantField)) {
          if (member is ICallable and not ConstantField) {

            var mem = (ICallable)member;
            if (member is Function { ByMethodDecl: { } } f) {
              mem = f.ByMethodDecl;
            }

            if (mem is Method { Body: not null } method) {
              AddMethodReveals(method);
            } else if (mem is Function { Body: not null } func) {
              AddFunctionReveals(func);
            }
          }
          
          else if (member is ConstantField { Rhs: not null} cf) {
            var subExpressions = cf.Rhs.SubExpressions;

            foreach (var expression in subExpressions) {
              if (expression is FunctionCallExpr funcExpr) {
                var func = funcExpr.Function;
                
                using IEnumerator<Function> enumerator = GetEnumerator(func, func.EnclosingClass, cf.Rhs.SubExpressions);
                while (enumerator.MoveNext()) {
                  var newFunc = enumerator.Current;
      
                  var origExpr = cf.Rhs;
                  var revealStmt = BuildRevealStmt(newFunc, cf.Rhs.Tok);

                  if (revealStmt is not null) {
                    var newExpr = new StmtExpr(cf.Rhs.Tok, revealStmt, origExpr) {
                      Type = origExpr.Type
                    };
                    cf.Rhs = newExpr;
                  }
                }
              }
            }
          }
        }
      } else if (decl is SubsetTypeDecl { Witness: not null } expr) {
        var functionCalls = expr.Constraint.SubExpressions.ToList().Concat(expr.Witness.SubExpressions.ToList());
        foreach (var expression in functionCalls) {
          if (expression is FunctionCallExpr funcExpr) {
            var func = funcExpr.Function;
            var revealStmt0 = BuildRevealStmt(func, expr.Witness.Tok);
            
            if (revealStmt0 is not null) {
              var newExpr = new StmtExpr(expr.Witness.Tok, revealStmt0, expr.Witness) {
                Type = expr.Witness.Type
              };
              expr.Witness = newExpr;
            }
              
            using IEnumerator<Function> enumerator = GetEnumerator(func, func.EnclosingClass, new List<Expression>());
            while (enumerator.MoveNext()) {
              var newFunc = enumerator.Current;
      
              var origExpr = expr.Witness;
              var revealStmt = BuildRevealStmt(newFunc, expr.Witness.Tok);

              if (revealStmt is not null) {
                var newExpr = new StmtExpr(expr.Witness.Tok, revealStmt, origExpr) {
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
    List<RevealStmt> addedReveals = new List<RevealStmt>();

    using IEnumerator<Function> enumerator = GetEnumerator(m, currentClass, m.SubExpressions);
    while (enumerator.MoveNext())
    {
      var func = enumerator.Current;
      var revealStmt = BuildRevealStmt(func, m.Tok);

      if (revealStmt is not null) {
        addedReveals.Add(revealStmt);
        m.Body.Body.Insert(0, revealStmt);
      }
    }

    if (m.Req.Any() || m.Ens.Any()) {
      Expression reqExpr = new LiteralExpr(m.Tok, true);
      reqExpr.Type = Type.Bool;
      foreach (var revealStmt0 in addedReveals) {
        reqExpr = new StmtExpr(reqExpr.tok, revealStmt0, reqExpr);
        reqExpr.Type = Type.Bool;
      }

      m.Req.Add(new AttributedExpression(reqExpr));
    }
  }
  
  
  private void AddFunctionReveals(Function f) {
    Contract.Requires(f != null);

    var currentClass = f.EnclosingClass;
    List<RevealStmt> addedReveals = new List<RevealStmt>();

    using IEnumerator<Function> enumerator = GetEnumerator(f, currentClass, f.SubExpressions);
    while (enumerator.MoveNext()) {
      var func = enumerator.Current;

      if (func == f) {
        continue;
      }
      
      var origExpr = f.Body;
      var revealStmt = BuildRevealStmt(func, f.Tok);

      if (revealStmt is not null) {
        addedReveals.Add(revealStmt);
        var newExpr = new StmtExpr(f.Tok, revealStmt, origExpr) {
          Type = origExpr.Type
        };
        f.Body = newExpr;
      }
    }

    if (f.Req.Any() || f.Ens.Any()) {
      Expression reqExpr = new LiteralExpr(f.Tok, true);
      reqExpr.Type = Type.Bool;
      foreach (var revealStmt0 in addedReveals) {
        reqExpr = new StmtExpr(reqExpr.tok, revealStmt0, reqExpr);
        reqExpr.Type = Type.Bool;
      }

      f.Req.Add(new AttributedExpression(reqExpr));
    }
  }
  
  private IEnumerator<Function> GetEnumerator(ICallable m, TopLevelDecl currentClass, IEnumerable<Expression> subexpressions) {
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

    Type[] typeList = exprListToTypeList(subexpressions.ToArray()).ToArray();
    
    typeList.Iter(newType => {
        if (newType is Type { AsSubsetType: not null } subsetType) {
          foreach (var subexpression in subsetType.AsSubsetType.Constraint.SubExpressions) {
            if (subexpression is FunctionCallExpr funcExpr) {
              var func = funcExpr.Function;
              var newVertex = func.EnclosingClass.EnclosingModuleDefinition.CallGraph.FindVertex(func);
              if (newVertex is not null) {
                queue.Enqueue(new GraphTraversalVertex(newVertex, false));
              }
            }
          }
        }
      }
    );

    // foreach (var expression in subexpressions) {
    //   if (expression.Type is Type { AsSubsetType: not null} subsetType) {
    //     foreach (var subexpression in subsetType.AsSubsetType.Constraint.SubExpressions) {
    //       if (subexpression is FunctionCallExpr funcExpr) {
    //         var func = funcExpr.Function;
    //         var newVertex = func.EnclosingClass.EnclosingModuleDefinition.CallGraph.FindVertex(func);
    //         if (newVertex is not null) {
    //           queue.Enqueue(new GraphTraversalVertex(newVertex, false));
    //         }
    //       }
    //     }
    //   }
    // }

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
        
        if (callable is Function { IsOpaque: false } func && func is not ExtremePredicate) {
          yield return func;
        }
      }
    }
  }

  private static IEnumerable<Type> exprListToTypeList(IEnumerable<Expression> exprList) {
    if (exprList is null || !exprList.Any()) {
      return new List<Type>();
    } 
    
    var subSubexpressionTypeList = exprList.Select(expr => exprListToTypeList(expr.SubExpressions));

    var subexpressionTypeList = exprList.Select(expr => expr.Type).ToArray();
    var subSubexpressionListConcat = subSubexpressionTypeList.SelectMany(x => x);
    
    return subexpressionTypeList.Concat(subSubexpressionListConcat);
  }

  private static RevealStmt BuildRevealStmt(Function callable, IToken tok) {

    Expression resolveExpr;

    var callableFullName = callable.FullDafnyName;

    var callableSeparatedName = callableFullName.Split(".");
    
    var callableSeparatedNameSegment =
      callableSeparatedName.Select(name => new NameSegment(tok, name, new List<Type>())).ToList();

    if (callableSeparatedNameSegment.Count() == 1) {
      resolveExpr = callableSeparatedNameSegment[0];
    } else  {
      if ((callableSeparatedNameSegment.Count() == 0)) {
        Contract.Assert(false);
      }
      
      var seed = new ExprDotName(tok, callableSeparatedNameSegment[0], callableSeparatedName[1], new List<Type>());
      resolveExpr = callableSeparatedName.Skip(2)
        .Aggregate(seed, (acc, name) => new ExprDotName(tok, acc, name, new List<Type>()));
    }
    
    List<Expression> expressionList = new List<Expression> {
      new ApplySuffix(tok, null,
        resolveExpr,
        new List<ActualBinding>(), tok)
    };

    var callableClass = ((TopLevelDeclWithMembers)callable.EnclosingClass);

    var callableName = "reveal_" + callable.Name;
    var member = callableClass.Members.Find(decl => decl.Name == callableName);
    
    var receiver = new StaticReceiverExpr(tok, new UserDefinedType(tok, callableName, callableClass, callableClass.TypeArgs.ConvertAll(obj => (Type) Type.Int) ), callableClass, true);

    if (member is null) {
      return null;
    }

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