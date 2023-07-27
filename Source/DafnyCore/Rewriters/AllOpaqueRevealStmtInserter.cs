using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny; 

/// <summary>
/// When Dafny is called with `--default-function-opacity autoRevealDependencies`, this rewriter computes
/// all transitive functional dependencies for each callable, and inserts reveal stmts for each such dependency
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
public class AllOpaqueRevealStmtInserter : IRewriter {
  public AllOpaqueRevealStmtInserter(ErrorReporter reporter) : base(reporter) { }

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
                var modulePath = new List<ModuleDefinition> { func.EnclosingClass.EnclosingModuleDefinition };
                
                if (isRevealedAlongPath(func, moduleDefinition, modulePath)) {
                  if (!func.IsOpaque && func.IsMadeImplicitlyOpaque(Options)) {
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

            if (isRevealedAlongPath(func, moduleDefinition, new List<ModuleDefinition> { func.EnclosingClass.EnclosingModuleDefinition })) {
              if (!func.IsOpaque && func.IsMadeImplicitlyOpaque(Options)) {
                var revealStmt0 = BuildRevealStmt(new FunctionReveal(func, new List<NameSegment>()), expr.Witness.Tok, moduleDefinition);

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
  /// Wrapper class created for traversing call graphs of modules. It stores the actual call graph vertex,
  /// a boolean flag `local` indicating whether the callable is in the same module as its predecessor in the traversal,
  /// and a sequence of NameSegments and ModuleDefinitions which captures the path from the original callable's EnclosingModule
  /// to this callable.
  /// </summary>
  private class GraphTraversalVertex {
    public readonly Graph<ICallable>.Vertex Vertex;
    public readonly bool Local;

    public List<NameSegment> NamePath;
    public List<ModuleDefinition> ModulePath;

    public GraphTraversalVertex(Graph<ICallable>.Vertex vertex, bool local, List<NameSegment> namePath, List<ModuleDefinition> modulePath) {
      Vertex = vertex;
      Local = local;
      NamePath = namePath;
      ModulePath = modulePath;
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

    bool autoRevealDeps = Attributes.ContainsBoolAtAnyLevel(m, "autoRevealDependencies", true);

    var currentClass = m.EnclosingClass;
    List<RevealStmt> addedReveals = new List<RevealStmt>();

    foreach (var func in GetEnumerator(m, currentClass, m.SubExpressions)) {
      var revealStmt = BuildRevealStmt(func, m.Tok, m.EnclosingClass.EnclosingModuleDefinition);

      if (revealStmt is not null) {
        addedReveals.Add(revealStmt);
        if (autoRevealDeps) {
          if (m is Constructor c) {
            c.BodyInit.Insert(0, revealStmt);
          } else {
            m.Body.Body.Insert(0, revealStmt);
          }
        }
      }
    }

    if (autoRevealDeps) {
      if (m.Req.Any() || m.Ens.Any()) {
        Expression reqExpr = new LiteralExpr(m.Tok, true);
        reqExpr.Type = Type.Bool;
        foreach (var revealStmt0 in addedReveals) {
          reqExpr = new StmtExpr(reqExpr.tok, revealStmt0, reqExpr);
          reqExpr.Type = Type.Bool;
        }

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
      if (func.function == f) {
        continue;
      }

      var origExpr = f.Body;
      var revealStmt = BuildRevealStmt(func, f.Tok, f.EnclosingClass.EnclosingModuleDefinition);

      if (revealStmt is not null) {
        addedReveals.Add(revealStmt);

        if (autoRevealDeps) {
          var newExpr = new StmtExpr(f.Tok, revealStmt, origExpr) {
            Type = origExpr.Type
          };
          f.Body = newExpr;
        }
      }
    }

    if (autoRevealDeps) {
      if (f.Req.Any() || f.Ens.Any()) {
        Expression reqExpr = new LiteralExpr(f.Tok, true);
        reqExpr.Type = Type.Bool;
        foreach (var revealStmt0 in addedReveals) {
          reqExpr = new StmtExpr(reqExpr.tok, revealStmt0, reqExpr);
          reqExpr.Type = Type.Bool;
        }

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

  private IEnumerable<FunctionReveal> GetEnumerator(ICallable m, TopLevelDecl currentClass, IEnumerable<Expression> subexpressions, ModuleDefinition rootModule = null) {
    var origVertex = currentClass.EnclosingModuleDefinition.CallGraph.FindVertex(m);
    var interModuleVertex = currentClass.EnclosingModuleDefinition.InterModuleCallGraph.FindVertex(m);

    if (origVertex is null) {
      yield break;
    }  //vertex can be null if m is a Test method.

    var visited = new HashSet<GraphTraversalVertex>();
    var queue = new Queue<GraphTraversalVertex>();

    var defaultNameSegmentPath = rootModule is null || rootModule == currentClass.EnclosingModuleDefinition
      ? new List<NameSegment>()
      : new List<NameSegment> { computeImportName(rootModule, currentClass.EnclosingModuleDefinition) };

    var defaultModulePath =
      rootModule is null || rootModule == currentClass.EnclosingModuleDefinition ? new List<ModuleDefinition>() : new List<ModuleDefinition> { currentClass.EnclosingModuleDefinition };

    var defaultRootModule = rootModule is null ? currentClass.EnclosingModuleDefinition : rootModule;

    // The rootModule parameter is used in the case when GetEnumerator is called, not on a function from a class, but on subset type expressions.
    // Here this function may be called with a callable that is in a different module than the original one. To capture this last part of scoping, this additional argument is used.

    foreach (var callable in origVertex.Successors) {
      queue.Enqueue(new GraphTraversalVertex(callable, true, defaultNameSegmentPath.ToList(), defaultModulePath.ToList()));
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
            var newVertex = func.EnclosingClass.EnclosingModuleDefinition.CallGraph.FindVertex(func);
            if (newVertex is not null) {
              queue.Enqueue(new GraphTraversalVertex(newVertex, false, defaultNameSegmentPath.ToList(), defaultModulePath.ToList()));
              //TODO implement proper name lookup above
            }
          }
        }
      }
    });

    if (interModuleVertex is not null) {
      foreach (var callable in interModuleVertex.Successors) {

        var newModulePath = defaultModulePath.ToList();
        newModulePath.Add(callable.N.EnclosingModule);

        if (isRevealedAlongPath(callable.N, defaultRootModule, newModulePath)) {
          var importName = computeImportName(defaultRootModule, callable.N.EnclosingModule);

          var newNameSegmentPath = defaultNameSegmentPath.ToList();

          if (importName is not null) {
            newNameSegmentPath.Add(importName);
          }

          queue.Enqueue(new GraphTraversalVertex(callable, false, newNameSegmentPath, newModulePath.ToList()));
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
          if (isRevealedAlongPath(vertex0.N, defaultRootModule, vertex.ModulePath)) {
            var newGraphTraversalVertex =
              new GraphTraversalVertex(vertex0, true, vertex.NamePath, vertex.ModulePath);

            if (!visited.Contains(newGraphTraversalVertex)) {
              queue.Enqueue(newGraphTraversalVertex);
            }

          }
        }

        if (interModuleGraphVertex is not null) {
          foreach (var vertex0 in interModuleGraphVertex.Successors) {
            var newNamePath = vertex.NamePath.ToList();
            var importName = computeImportName(graphVertex.N.EnclosingModule, vertex0.N.EnclosingModule);

            if (importName is not null) {
              newNamePath.Add(importName);
            }

            var newModulePath = vertex.ModulePath.ToList();
            newModulePath.Add(vertex0.N.EnclosingModule);

            if (isRevealedAlongPath(vertex0.N, defaultRootModule, newModulePath)) {
              queue.Enqueue(new GraphTraversalVertex(vertex0, false, newNamePath, newModulePath));
            }

          }
        }

        var callable = graphVertex.N;

        if (callable is Function { IsOpaque: false } func && func.IsMadeImplicitlyOpaque(Options)) {
          yield return new FunctionReveal(func, vertex.NamePath.ToList());
        }
      }
    }
  }

  private bool isRevealedAlongPath(ICallable callable, ModuleDefinition origModule, List<ModuleDefinition> modulePath) {

    var accum = true;

    var modulePathLocalCopy = modulePath.ToList();
    modulePathLocalCopy.Reverse();

    string nameAccum = callable.NameRelativeToModule;

    if (!modulePathLocalCopy.Any()) {
      return true;
    }

    modulePathLocalCopy.Add(origModule);

    for (var i = 0; i < modulePathLocalCopy.Count() - 1; i++) {
      var exportSet = FindModuleExportSet(modulePathLocalCopy[i + 1], modulePathLocalCopy[i]);

      foreach (ModuleExportDecl modExportDecl in modulePathLocalCopy[i].TopLevelDecls.Where(decl => decl is ModuleExportDecl && decl.Name == exportSet)) {
        var isItExported = false;
        foreach (ExportSignature export in modExportDecl.Exports) {
          if (export.Decl.Name == nameAccum && !export.Opaque) {
            isItExported = true;
          }
        }

        if (!isItExported) {
          accum = false;
        }
        var importName = computeImportName(modulePathLocalCopy[i + 1], modulePathLocalCopy[i]);

        if (importName is not null) {
          nameAccum = importName.Name + "." + nameAccum;
        }
      }
    }

    return accum;
  }

  private string FindModuleExportSet(ModuleDefinition origMod, ModuleDefinition importedMod) {
    foreach (AliasModuleDecl aliasModDecl in origMod.TopLevelDecls.Where(decl => decl is AliasModuleDecl)) {
      if (aliasModDecl.TargetQId.Root.FullDafnyName == importedMod.FullDafnyName) {
        return aliasModDecl.Exports.Any() ? aliasModDecl.Exports.First().val : importedMod.Name;
      }
    }

    if (importedMod.IsAbstract) {
      Contract.Assert(importedMod.FullName[^4..] == ".Abs");
      var importedModuleName = importedMod.FullName[..^4]; //Remove .Abs at the end

      foreach (AbstractModuleDecl abstractModuleDecl in origMod.TopLevelDecls.Where(decl => decl is AbstractModuleDecl)) {
        if (abstractModuleDecl.FullName == importedModuleName) {
          return abstractModuleDecl.Exports.Any() ? abstractModuleDecl.Exports.First().val : importedMod.Name;
        }
      }
    }

    return importedMod.Name;
  }

  private NameSegment computeImportName(ModuleDefinition origModule, ModuleDefinition newModule) {
    foreach (AliasModuleDecl aliasModDecl in origModule.TopLevelDecls.Where(decl => decl is AliasModuleDecl)) {
      if (aliasModDecl.TargetQId.Root.FullDafnyName == newModule.FullDafnyName) {
        return new NameSegment(aliasModDecl.tok, aliasModDecl.Name, new List<Type>());
      }
    }

    if (newModule.IsAbstract) {
      Contract.Assert(newModule.FullName[^4..] == ".Abs");
      var newModuleName = newModule.FullName[..^4]; //Remove .Abs at the end

      foreach (AbstractModuleDecl abstractModuleDecl in origModule.TopLevelDecls.Where(decl => decl is AbstractModuleDecl)) {
        if (abstractModuleDecl.FullName == newModuleName) {
          return new NameSegment(abstractModuleDecl.tok, abstractModuleDecl.Name, new List<Type>());
        }
      }
    }

    // otherwise newModule is available in an opened state in origModule
    return null;
  }

  struct FunctionReveal {
    public Function function;
    public List<NameSegment> namePath;

    public FunctionReveal(Function func, List<NameSegment> namePath) {
      this.function = func;
      this.namePath = namePath;
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

  private static RevealStmt BuildRevealStmt(FunctionReveal func, IToken tok, ModuleDefinition currentModule) {
    if (func.function.EnclosingClass.Name != "_default") {
      List<Type> args = new List<Type>();
      for (int i = 0; i < func.function.EnclosingClass.TypeArgs.Count(); i++) {
        args.Add(new IntType());
      }

      func.namePath.Add(new NameSegment(tok, func.function.EnclosingClass.Name, args));
    }

    func.namePath.Add(new NameSegment(tok, func.function.Name, new List<Type>()));

    Expression nameSeed = func.namePath[0];
    var resolveExpr = func.namePath.Skip(1)
      .Aggregate(nameSeed, (acc, name) => new ExprDotName(tok, acc, name.Name, name.OptTypeArguments));

    var callableClass = ((TopLevelDeclWithMembers)func.function.EnclosingClass);

    var callableName = "reveal_" + func.function.Name;
    var member = callableClass.Members.Find(decl => decl.Name == callableName);

    var receiver = new StaticReceiverExpr(tok, new UserDefinedType(tok, callableName, callableClass, callableClass.TypeArgs.ConvertAll(obj => (Type)Type.Int)), callableClass, true);

    if (member is null) {
      return null;
    }

    callableName = ((ICallable)member).NameRelativeToModule;
    var rr = new MemberSelectExpr(func.function.Tok, receiver, callableName);
    rr.Type = new InferredTypeProxy();
    rr.Member = member;
    rr.TypeApplication_JustMember = new List<Type>();
    rr.TypeApplication_AtEnclosingClass = new List<Type>();

    var call = new CallStmt(func.function.RangeToken, new List<Expression>(), rr, new List<ActualBinding>(),
      func.function.Tok);
    call.IsGhost = true;
    call.Bindings.AcceptArgumentExpressionsAsExactParameterList(new List<Expression>());

    resolveExpr.Type = new InferredTypeProxy();
    ((ConcreteSyntaxExpression)resolveExpr).ResolvedExpression = rr;

    List<Expression> expressionList = new List<Expression> {
      new ApplySuffix(tok, null,
        resolveExpr,
        new List<ActualBinding>(), tok)
    };

    var revealStmt = new RevealStmt(func.function.RangeToken, expressionList);
    revealStmt.ResolvedStatements.Add(call);
    revealStmt.IsGhost = true;

    return revealStmt;
  }
  
  private static RevealStmt BuildRevealStmt(Function func, IToken tok, ModuleDefinition currentModule) {
    return BuildRevealStmt(new FunctionReveal(func, new List<NameSegment>()), tok, currentModule);
  }
}