using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny; 

/// <summary>
/// When Dafny is called with `--default-function-opacity autoRevealDependencies`, this rewriter computes
/// all transitive functional dependencies for each callable, and inserts (in-memory, on the AST) reveal stmts for each such dependency
/// at the top of the callable body, and also in a precondition.
///
/// For example:
///   function f()
///     ensures true
///   { g(h()) }
///
/// would get transformed to:
///   function f()
///     requires reveal g(); reveal h(); true
///     ensures true
///   {
///     reveal g(); reveal h();
///     g(h())
///   }
///
/// assuming that g() and h() don't have the `{:transparent}` attribute.
/// </summary>
public class AutoRevealFunctionDependencies : IRewriter {
  public AutoRevealFunctionDependencies(ErrorReporter reporter) : base(reporter) { }

  internal override void PostResolveIntermediate(ModuleDefinition moduleDefinition) {
    Contract.Requires(moduleDefinition != null);

    foreach (var decl in moduleDefinition.TopLevelDecls) {
      if (decl is TopLevelDeclWithMembers cl) {
        foreach (var member in cl.Members) {
          if (member is ICallable and not ConstantField) {
            var mem = (ICallable)member;
            if (member is Function { ByMethodDecl: not null } f) {
              mem = f.ByMethodDecl;
            }

            if (mem is Method { Body: not null } method) {
              AddMethodReveals(method, Reporter);
            } else if (mem is Function { Body: not null } func) {
              AddFunctionReveals(func, Reporter);
            }
          } else if (member is ConstantField { Rhs: not null } cf) {
            var subExpressions = cf.Rhs.SubExpressions;

            foreach (var expression in subExpressions) {
              if (expression is FunctionCallExpr funcExpr) {
                var func = funcExpr.Function;

                if (isRevealable(moduleDefinition.AccessibleMembers, func)) {
                  if (func.IsMadeImplicitlyOpaque(Options)) {
                    var expr = cf.Rhs;

                    var revealStmt0 = BuildRevealStmt(func,
                      expr.Tok, moduleDefinition);

                    if (revealStmt0 is not null) {
                      var newExpr = new StmtExpr(expr.Tok, revealStmt0, expr) {
                        Type = expr.Type
                      };
                      cf.Rhs = newExpr;
                    }
                  }

                  foreach (var newFunc in GetEnumerator(func, func.EnclosingClass, new List<Expression> { cf.Rhs }, moduleDefinition)) {
                    var origExpr = cf.Rhs;
                    var revealStmt = BuildRevealStmt(newFunc, cf.Rhs.Tok, moduleDefinition);

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
        }
      } else if (decl is SubsetTypeDecl { Witness: not null } expr) {
        var expressions = expr.Constraint.SubExpressions.ToList().Concat(expr.Witness.SubExpressions.ToList());
        foreach (var expression in expressions) {
          if (expression is FunctionCallExpr funcExpr) {
            var func = funcExpr.Function;

            if (isRevealable(moduleDefinition.AccessibleMembers, func)) {
              if (func.IsMadeImplicitlyOpaque(Options)) {
                var revealStmt0 = BuildRevealStmt(func, expr.Witness.Tok, moduleDefinition);

                if (revealStmt0 is not null) {
                  var newExpr = new StmtExpr(expr.Witness.Tok, revealStmt0, expr.Witness) {
                    Type = expr.Witness.Type
                  };
                  expr.Witness = newExpr;
                }
              }

              foreach (var newFunc in GetEnumerator(func, func.EnclosingClass, new List<Expression>(), moduleDefinition)) {
                var origExpr = expr.Witness;
                var revealStmt = BuildRevealStmt(newFunc, expr.Witness.Tok, moduleDefinition);

                if (revealStmt is not null) {
                  var newExpr = new StmtExpr(expr.Witness.Tok, revealStmt, origExpr) {
                    Type = origExpr.Type
                  };
                  expr.Witness = newExpr;
                }
              }
            }
          }
        }
      }
    }
  }

  /// <summary>
  /// Wrapper class created for traversing call graphs of modules. It stores the actual call graph vertex and
  /// a boolean flag `local` indicating whether the callable is in the same module as its predecessor in the traversal.
  /// </summary>
  private class GraphTraversalVertex {
    public readonly Graph<ICallable>.Vertex Vertex;
    public readonly bool Local;

    public GraphTraversalVertex(Graph<ICallable>.Vertex vertex, bool local) {
      Vertex = vertex;
      Local = local;
    }

    public override bool Equals(object obj) {
      var other = obj as GraphTraversalVertex;
      return other?.Vertex.N.FullSanitizedName == Vertex.N.FullSanitizedName;
    }

    public override int GetHashCode() {
      return HashCode.Combine(Vertex.N.FullSanitizedName);
    }
  }

  private void AddMethodReveals(Method m, ErrorReporter reporter) {
    Contract.Requires(m != null);

    var autoRevealDeps = Attributes.ContainsBoolAtAnyLevel(m, "autoRevealDependencies", true);

    var currentClass = m.EnclosingClass;
    List<RevealStmt> addedReveals = new List<RevealStmt>();

    foreach (var func in GetEnumerator(m, currentClass, m.SubExpressions)) {
      var revealStmt = BuildRevealStmt(func, m.Tok, m.EnclosingClass.EnclosingModuleDefinition);

      if (revealStmt is not null) {
        addedReveals.Add(revealStmt);
      }
    }

    if (autoRevealDeps) {
      Expression reqExpr = new LiteralExpr(m.Tok, true) {
        Type = Type.Bool
      };

      foreach (var revealStmt in addedReveals) {
        if (m is Constructor c) {
          c.BodyInit.Insert(0, revealStmt);
        } else {
          m.Body.Body.Insert(0, revealStmt);
        }

        reqExpr = new StmtExpr(reqExpr.tok, revealStmt, reqExpr) {
          Type = Type.Bool
        };
      }

      if (m.Req.Any() || m.Ens.Any()) {
        m.Req.Insert(0, new AttributedExpression(reqExpr));
      }
    }

    if (addedReveals.Any()) {
      reporter.Message(MessageSource.Rewriter, ErrorLevel.Info, null, m.tok, $"{addedReveals.Count} reveal statement{(addedReveals.Count > 1 ? "s" : "")} inserted: \n{RenderRevealStmts(addedReveals)}");
    }
  }

  private void AddFunctionReveals(Function f, ErrorReporter reporter) {
    Contract.Requires(f != null);

    bool autoRevealDeps = Attributes.ContainsBoolAtAnyLevel(f, "autoRevealDependencies", true);

    var currentClass = f.EnclosingClass;
    List<RevealStmt> addedReveals = new List<RevealStmt>();

    foreach (var func in GetEnumerator(f, currentClass, f.SubExpressions)) {
      if (func == f) {
        continue;
      }

      var revealStmt = BuildRevealStmt(func, f.Tok, f.EnclosingClass.EnclosingModuleDefinition);

      if (revealStmt is not null) {
        addedReveals.Add(revealStmt);
      }
    }

    if (autoRevealDeps) {
      Expression reqExpr = new LiteralExpr(f.Tok, true);
      reqExpr.Type = Type.Bool;

      var bodyExpr = f.Body;

      foreach (var revealStmt in addedReveals) {
        bodyExpr = new StmtExpr(f.Tok, revealStmt, bodyExpr) {
          Type = bodyExpr.Type
        };

        reqExpr = new StmtExpr(reqExpr.tok, revealStmt, reqExpr) {
          Type = Type.Bool
        };
      }

      f.Body = bodyExpr;

      if (f.Req.Any() || f.Ens.Any()) {
        f.Req.Insert(0, new AttributedExpression(reqExpr));
      }
    }

    if (addedReveals.Any()) {
      reporter.Message(MessageSource.Rewriter, ErrorLevel.Info, null, f.tok, $"{addedReveals.Count} reveal statement{(addedReveals.Count > 1 ? "s" : "")} inserted: \n{RenderRevealStmts(addedReveals)}");
    }
  }

  private static string RenderRevealStmts(List<RevealStmt> revealStmtList) {
    Contract.Requires(revealStmtList.Any());
    return string.Join(" ", revealStmtList);
  }

  private IEnumerable<Function> GetEnumerator(ICallable m, TopLevelDecl currentClass, IEnumerable<Expression> subexpressions, ModuleDefinition rootModule = null) {
    var origVertex = currentClass.EnclosingModuleDefinition.CallGraph.FindVertex(m);
    var interModuleVertex = currentClass.EnclosingModuleDefinition.InterModuleCallGraph.FindVertex(m);

    if (origVertex is null) {
      yield break;
    }  //vertex can be null if m is a Test method.

    var visited = new HashSet<GraphTraversalVertex>();
    var queue = new Queue<GraphTraversalVertex>();

    var defaultRootModule = rootModule is null ? currentClass.EnclosingModuleDefinition : rootModule;

    // The rootModule parameter is used in the case when GetEnumerator is called, not on a function from a class, but on subset type expressions.
    // Here this function may be called with a callable that is in a different module than the original one.

    foreach (var callable in origVertex.Successors) {
      queue.Enqueue(new GraphTraversalVertex(callable, true));
    }

    var typeList = ExprListToTypeList(subexpressions.ToList()).ToList();

    if (m is Function f) {
      typeList.Add(f.ResultType);
    }

    typeList.ForEach(newType => {
      if (newType is Type { AsSubsetType: not null }) {
        foreach (var subexpression in newType.AsSubsetType.Constraint.SubExpressions) {
          if (subexpression is FunctionCallExpr funcExpr) {
            var func = funcExpr.Function;

            if (isRevealable(defaultRootModule.AccessibleMembers, func)) {
              var newVertex = func.EnclosingClass.EnclosingModuleDefinition.CallGraph.FindVertex(func);

              if (newVertex is not null) {
                queue.Enqueue(new GraphTraversalVertex(newVertex, false));
              }
            }
          }
        }
      }
    });

    if (interModuleVertex is not null) {
      foreach (var callable in interModuleVertex.Successors) {

        if (isRevealable(defaultRootModule.AccessibleMembers, (Declaration)callable.N)) {

          queue.Enqueue(new GraphTraversalVertex(callable, false));
        }
      }
    }

    while (queue.Any()) {
      var vertex = queue.Dequeue();
      if (!visited.Contains(vertex)) {
        visited.Add(vertex);

        Graph<ICallable>.Vertex graphVertex;
        Graph<ICallable>.Vertex interModuleGraphVertex;

        if (vertex.Local) {
          graphVertex = vertex.Vertex;

        } else {
          graphVertex = vertex.Vertex.N.EnclosingModule.CallGraph.FindVertex(vertex.Vertex.N);

          if (graphVertex is null) {
            continue;
          }
        }

        interModuleGraphVertex = graphVertex.N.EnclosingModule.InterModuleCallGraph.FindVertex(graphVertex.N);

        foreach (var vertex0 in graphVertex.Successors) {
          if (isRevealable(defaultRootModule.AccessibleMembers, (Declaration)vertex0.N)) {
            var newGraphTraversalVertex =
              new GraphTraversalVertex(vertex0, true);

            if (!visited.Contains(newGraphTraversalVertex)) {
              queue.Enqueue(newGraphTraversalVertex);
            }
          }
        }

        if (interModuleGraphVertex is not null) {
          foreach (var vertex0 in interModuleGraphVertex.Successors) {
            if (isRevealable(defaultRootModule.AccessibleMembers, (Declaration)vertex0.N)) {
              queue.Enqueue(new GraphTraversalVertex(vertex0, false));
            }
          }
        }

        var callable = graphVertex.N;

        if (callable is Function func && func.IsMadeImplicitlyOpaque(Options)) {
          yield return func;
        }
      }
    }
  }

  private static IEnumerable<Type> ExprListToTypeList(IEnumerable<Expression> exprList) {
    if (exprList is null || !exprList.Any()) {
      return new List<Type>();
    }

    var subExprTypeList = exprList.Select(expr => ExprListToTypeList(expr.SubExpressions));

    var typeList = exprList.Select(expr => expr.Type);
    var subExprTypeListConcat = subExprTypeList.SelectMany(x => x);

    return typeList.Concat(subExprTypeListConcat);
  }

  private static RevealStmt BuildRevealStmt(Function func, IToken tok, ModuleDefinition rootModule) {
    if (func.EnclosingClass.Name != "_default") {
      List<Type> args = new List<Type>();
      for (int i = 0; i < func.EnclosingClass.TypeArgs.Count(); i++) {
        args.Add(new IntType());
      }

    }

    ModuleDefinition.AccessibleMember accessibleMember = null;

    try {
      accessibleMember = rootModule.AccessibleMembers[func][0];
    } catch (KeyNotFoundException) {
      Contract.Assert(false);
    }
    var resolveExpr = constructExpressionFromPath(func, accessibleMember);

    var callableClass = ((TopLevelDeclWithMembers)func.EnclosingClass);

    var callableName = "reveal_" + func.Name;
    var member = callableClass.Members.Find(decl => decl.Name == callableName);

    var receiver = new StaticReceiverExpr(tok, new UserDefinedType(tok, callableName, callableClass, callableClass.TypeArgs.ConvertAll(obj => (Type)Type.Int)), callableClass, true);

    if (member is null) {
      return null;
    }

    callableName = ((ICallable)member).NameRelativeToModule;
    var rr = new MemberSelectExpr(func.Tok, receiver, callableName);
    rr.Type = new InferredTypeProxy();
    rr.Member = member;
    rr.TypeApplication_JustMember = new List<Type>();
    rr.TypeApplication_AtEnclosingClass = new List<Type>();

    var call = new CallStmt(func.RangeToken, new List<Expression>(), rr, new List<ActualBinding>(),
      func.Tok);
    call.IsGhost = true;
    call.Bindings.AcceptArgumentExpressionsAsExactParameterList(new List<Expression>());

    resolveExpr.Type = new InferredTypeProxy();
    ((ConcreteSyntaxExpression)resolveExpr).ResolvedExpression = rr;

    List<Expression> expressionList = new List<Expression> {
      new ApplySuffix(tok, null,
        resolveExpr,
        new List<ActualBinding>(), tok)
    };

    var revealStmt = new RevealStmt(func.RangeToken, expressionList);
    revealStmt.ResolvedStatements.Add(call);
    revealStmt.IsGhost = true;

    return revealStmt;
  }

  private static Expression constructExpressionFromPath(Function func, ModuleDefinition.AccessibleMember accessibleMember) {

    var topLevelDeclsList = accessibleMember.AccessPath;
    var nameList = topLevelDeclsList.Select(decl => new NameSegment(func.tok, decl.Name, new List<Type>())).ToList();
    // TODO: Add class type args.

    nameList.Add(new NameSegment(func.tok, func.Name, new List<Type>()));

    Expression nameSeed = nameList[0];
    var resolveExpr = nameList.Skip(1)
    .Aggregate(nameSeed, (acc, name) => new ExprDotName(func.tok, acc, name.Name, name.OptTypeArguments));

    return resolveExpr;
  }

  private static bool isRevealable(Dictionary<Declaration, List<ModuleDefinition.AccessibleMember>> accessibleMembers,
    Declaration decl) {
    if (accessibleMembers.ContainsKey(decl)) {
      return accessibleMembers[decl][0].IsRevealed;
    }

    return false;
  }
}