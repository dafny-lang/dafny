using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;

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
  public AutoRevealFunctionDependencies(ErrorReporter reporter) : base(reporter) {
  }

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

                if (IsRevealable(moduleDefinition.AccessibleMembers, func)) {
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

                  foreach (var newFunc in GetEnumerator(func, func.EnclosingClass, new List<Expression> { cf.Rhs },
                             moduleDefinition)) {
                    var origExpr = cf.Rhs;
                    var revealStmt = BuildRevealStmt(newFunc.Function, cf.Rhs.Tok, moduleDefinition);

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

            if (IsRevealable(moduleDefinition.AccessibleMembers, func)) {
              if (func.IsMadeImplicitlyOpaque(Options)) {
                var revealStmt0 = BuildRevealStmt(func, expr.Witness.Tok, moduleDefinition);

                if (revealStmt0 is not null) {
                  var newExpr = new StmtExpr(expr.Witness.Tok, revealStmt0, expr.Witness) {
                    Type = expr.Witness.Type
                  };
                  expr.Witness = newExpr;
                }
              }

              foreach (var newFunc in GetEnumerator(func, func.EnclosingClass, new List<Expression>(),
                         moduleDefinition)) {
                var origExpr = expr.Witness;
                var revealStmt = BuildRevealStmt(newFunc.Function, expr.Witness.Tok, moduleDefinition);

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
    public readonly int Depth;

    public GraphTraversalVertex(Graph<ICallable>.Vertex vertex, bool local, int depth) {
      Vertex = vertex;
      Local = local;
      Depth = depth;
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

    object autoRevealDepsVal = null;
    bool autoRevealDeps = Attributes.ContainsMatchingValue(m.Attributes, "autoRevealDependencies",
      ref autoRevealDepsVal, new List<Attributes.MatchingValueOption> {
        Attributes.MatchingValueOption.Bool,
        Attributes.MatchingValueOption.Int
      }, s => Reporter.Error(MessageSource.Rewriter, ErrorLevel.Error, m.Tok, s));

    // Default behavior is reveal all dependencies
    int autoRevealDepth = int.MaxValue;

    if (autoRevealDeps) {
      if (autoRevealDepsVal is false) {
        autoRevealDepth = 0;
      } else if (autoRevealDepsVal is BigInteger i) {
        autoRevealDepth = (int)i;
      }
    }

    var currentClass = m.EnclosingClass;
    List<RevealStmtWithDepth> addedReveals = new();

    foreach (var func in GetEnumerator(m, currentClass, m.SubExpressions)) {
      var revealStmt = BuildRevealStmt(func.Function, m.Tok, m.EnclosingClass.EnclosingModuleDefinition);

      if (revealStmt is not null) {
        addedReveals.Add(new RevealStmtWithDepth(revealStmt, func.Depth));
      }
    }

    if (autoRevealDepth > 0) {
      Expression reqExpr = new LiteralExpr(m.Tok, true) {
        Type = Type.Bool
      };

      foreach (var revealStmt in addedReveals) {
        if (revealStmt.Depth <= autoRevealDepth) {
          if (m is Constructor c) {
            c.BodyInit.Insert(0, revealStmt.RevealStmt);
          } else {
            m.Body.Body.Insert(0, revealStmt.RevealStmt);
          }

          reqExpr = new StmtExpr(reqExpr.tok, revealStmt.RevealStmt, reqExpr) {
            Type = Type.Bool
          };
        } else {
          break;
        }
      }

      if (m.Req.Any() || m.Ens.Any()) {
        m.Req.Insert(0, new AttributedExpression(reqExpr));
      }
    }

    if (addedReveals.Any()) {
      var numInsertedReveals = addedReveals.Count(stmt => stmt.Depth <= autoRevealDepth);
      var renderedRevealStmts = RenderRevealStmts(addedReveals, 1 + autoRevealDepth);
      
      reporter.Message(MessageSource.Rewriter, ErrorLevel.Info, null, m.tok,
        $"Total {addedReveals.Count} function dependenc{(addedReveals.Count == 1 ? "y" : "ies")} found. {numInsertedReveals} reveal statement{(numInsertedReveals == 1 ? "" : "s")} inserted implicitly.{(numInsertedReveals < addedReveals.Count ? " Remaining:\n" + renderedRevealStmts : "")}");
    }
  }

  private void AddFunctionReveals(Function f, ErrorReporter reporter) {
    Contract.Requires(f != null);

    object autoRevealDepsVal = null;
    bool autoRevealDeps = Attributes.ContainsMatchingValue(f.Attributes, "autoRevealDependencies",
      ref autoRevealDepsVal, new List<Attributes.MatchingValueOption> {
        Attributes.MatchingValueOption.Bool,
        Attributes.MatchingValueOption.Int
      }, s => Reporter.Error(MessageSource.Rewriter, ErrorLevel.Error, f.Tok, s));

    // Default behavior is reveal all dependencies
    int autoRevealDepth = int.MaxValue;

    if (autoRevealDeps) {
      if (autoRevealDepsVal is false) {
        autoRevealDepth = 0;
      } else if (autoRevealDepsVal is BigInteger i) {
        autoRevealDepth = (int)i;
      }
    }
    
    var currentClass = f.EnclosingClass;
    List<RevealStmtWithDepth> addedReveals = new();

    foreach (var func in GetEnumerator(f, currentClass, f.SubExpressions)) {
      var revealStmt = BuildRevealStmt(func.Function, f.Tok, f.EnclosingClass.EnclosingModuleDefinition);

      if (revealStmt is not null) {
        addedReveals.Add(new RevealStmtWithDepth(revealStmt, func.Depth));
      }
    }

    if (autoRevealDepth > 0) {
      Expression reqExpr = new LiteralExpr(f.Tok, true);
      reqExpr.Type = Type.Bool;

      var bodyExpr = f.Body;

      foreach (var revealStmt in addedReveals) {
        if (revealStmt.Depth <= autoRevealDepth) {
          bodyExpr = new StmtExpr(f.Tok, revealStmt.RevealStmt, bodyExpr) {
            Type = bodyExpr.Type
          };

          reqExpr = new StmtExpr(reqExpr.tok, revealStmt.RevealStmt, reqExpr) {
            Type = Type.Bool
          };
        } else {
          break;
        }
      }

      f.Body = bodyExpr;

      if (f.Req.Any() || f.Ens.Any()) {
        f.Req.Insert(0, new AttributedExpression(reqExpr));
      }
    }

    if (addedReveals.Any()) {
      var numInsertedReveals = addedReveals.Count(stmt => stmt.Depth <= autoRevealDepth);
      var renderedRevealStmts = RenderRevealStmts(addedReveals, 1 + autoRevealDepth);

      reporter.Message(MessageSource.Rewriter, ErrorLevel.Info, null, f.tok,
        $"Total {addedReveals.Count} function dependenc{(addedReveals.Count == 1 ? "y" : "ies")} found. {numInsertedReveals} reveal statement{(numInsertedReveals == 1 ? "" : "s")} inserted implicitly.{(numInsertedReveals < addedReveals.Count ? " Remaining:\n" + renderedRevealStmts : "")}");
    }
  }

  private static string RenderRevealStmts(List<RevealStmtWithDepth> addedRevealStmtList, int depth) {
    Contract.Requires(addedRevealStmtList.Any());

    var currentDepth = depth;

    string result = $"// depth {currentDepth}: {addedRevealStmtList.Count(stmt => stmt.Depth == currentDepth)} stmts\n";

    foreach (var revealStmt in addedRevealStmtList) {
      if (revealStmt.Depth > currentDepth) {
        currentDepth = revealStmt.Depth;
        result += $"\n\n// depth {currentDepth}: {addedRevealStmtList.Count(stmt => stmt.Depth == currentDepth)} stmts\n";
      }  
      
      if (revealStmt.Depth == currentDepth) {
        result += $"{revealStmt.RevealStmt} ";
      }


    }
    return result;
  }

  private record RevealStmtWithDepth(RevealStmt RevealStmt, int Depth);

  private record FunctionWithDepth(Function Function, int Depth);

  private IEnumerable<FunctionWithDepth> GetEnumerator(ICallable m, TopLevelDecl currentClass, IEnumerable<Expression> subexpressions, ModuleDefinition rootModule = null) {
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
      queue.Enqueue(new GraphTraversalVertex(callable, true, 1));
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

            if (IsRevealable(defaultRootModule.AccessibleMembers, func)) {
              var newVertex = func.EnclosingClass.EnclosingModuleDefinition.CallGraph.FindVertex(func);

              if (newVertex is not null) {
                queue.Enqueue(new GraphTraversalVertex(newVertex, false, 1));
              }
            }
          }
        }
      }
    });

    if (interModuleVertex is not null) {
      foreach (var callable in interModuleVertex.Successors) {

        if (IsRevealable(defaultRootModule.AccessibleMembers, (Declaration)callable.N)) {

          queue.Enqueue(new GraphTraversalVertex(callable, false, 1));
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
          if (IsRevealable(defaultRootModule.AccessibleMembers, (Declaration)vertex0.N)) {
            var newGraphTraversalVertex =
              new GraphTraversalVertex(vertex0, true, 1+vertex.Depth);

            if (!visited.Contains(newGraphTraversalVertex)) {
              queue.Enqueue(newGraphTraversalVertex);
            }
          }
        }

        if (interModuleGraphVertex is not null) {
          foreach (var vertex0 in interModuleGraphVertex.Successors) {
            if (IsRevealable(defaultRootModule.AccessibleMembers, (Declaration)vertex0.N)) {
              queue.Enqueue(new GraphTraversalVertex(vertex0, false, 1+vertex.Depth));
            }
          }
        }

        var callable = graphVertex.N;

        if (callable is Function func && func.IsMadeImplicitlyOpaque(Options)) {
          yield return new FunctionWithDepth(func, vertex.Depth);
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
    List<Type> args = new List<Type>();
    foreach (var _ in func.EnclosingClass.TypeArgs) {
      args.Add(new IntType());
    }

    ModuleDefinition.AccessibleMember accessibleMember = null;

    try {
      accessibleMember = rootModule.AccessibleMembers[func].First(member => member.IsRevealed);
    } catch (KeyNotFoundException) {
      Contract.Assert(false);
    }
    var resolveExpr = ConstructExpressionFromPath(func, accessibleMember);

    var callableClass = ((TopLevelDeclWithMembers)func.EnclosingClass);

    var callableName = "reveal_" + func.Name;
    var member = callableClass.Members.Find(decl => decl.Name == callableName);

    Type.PushScope(callableClass.EnclosingModuleDefinition.VisibilityScope);
    var receiver = new StaticReceiverExpr(tok, new UserDefinedType(tok, callableName, callableClass, callableClass.TypeArgs.ConvertAll(obj => (Type)Type.Int)), callableClass, true);
    Type.PopScope(callableClass.EnclosingModuleDefinition.VisibilityScope);

    if (member is null) {
      return null;
    }

    callableName = ((ICallable)member).NameRelativeToModule;
    var rr = new MemberSelectExpr(func.Tok, receiver, callableName);
    rr.Type = new InferredTypeProxy();
    rr.Member = member;
    rr.TypeApplication_JustMember = new List<Type>();
    rr.TypeApplication_AtEnclosingClass = args;

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

  private static Expression ConstructExpressionFromPath(Function func, ModuleDefinition.AccessibleMember accessibleMember) {

    var topLevelDeclsList = accessibleMember.AccessPath;
    var nameList = topLevelDeclsList.Where(decl => decl.Name != "_default").Select(decl => TopLevelDeclToNameSegment(decl, func.tok)).ToList();

    nameList.Add(new NameSegment(func.tok, func.Name, new List<Type>()));

    Expression nameSeed = nameList[0];
    var resolveExpr = nameList.Skip(1)
    .Aggregate(nameSeed, (acc, name) => new ExprDotName(func.tok, acc, name.Name, name.OptTypeArguments));

    return resolveExpr;
  }

  private static NameSegment TopLevelDeclToNameSegment(TopLevelDecl decl, IToken tok) {
    var typeArgs = new List<Type>();

    foreach (var arg in decl.TypeArgs) {
      typeArgs.Add(new IntType());
    }

    return new NameSegment(tok, decl.Name, typeArgs);
  }

  private static bool IsRevealable(Dictionary<Declaration, List<ModuleDefinition.AccessibleMember>> accessibleMembers,
    Declaration decl) {
    if (accessibleMembers.TryGetValue(decl, out var memberList)) {
      return memberList.Exists(member => member.IsRevealed);
    }

    return false;
  }
}