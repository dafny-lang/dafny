using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Linq.Expressions;
using Microsoft.Boogie;
using Microsoft.Dafny.Plugins;

namespace Microsoft.Dafny; 

public class AllOpaqueRevealStmtInserter : IRewriter {
  public AllOpaqueRevealStmtInserter(ErrorReporter reporter) : base(reporter) { }
  
  internal override void PostResolveIntermediate(ModuleDefinition moduleDefinition) {
    Contract.Requires(moduleDefinition != null);

    foreach (var decl in moduleDefinition.TopLevelDecls) {
      if (decl is TopLevelDeclWithMembers cl) {
        foreach (var member in cl.Members) {
          if (member is ICallable and not ConstantField) {

            var mem = (ICallable)member;
            if (member is Function { ByMethodDecl: { } } f) {
              mem = f.ByMethodDecl;
            }

            if (mem is Method { Body: not null } method) {
              AddMethodReveals(method, Reporter);
            } else if (mem is Function { Body: not null } func) {
              AddFunctionReveals(func, Reporter);
            }
          }
          
          else if (member is ConstantField { Rhs: not null} cf) {
            var subExpressions = cf.Rhs.SubExpressions;

            foreach (var expression in subExpressions) {
              if (expression is FunctionCallExpr funcExpr) {
                var func = funcExpr.Function;
                
                using IEnumerator<FunctionReveal> enumerator = GetEnumerator(func, func.EnclosingClass, cf.Rhs.SubExpressions);
                while (enumerator.MoveNext()) {
                  var newFunc = enumerator.Current;
      
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
      } else if (decl is SubsetTypeDecl { Witness: not null } expr) {
        var functionCalls = expr.Constraint.SubExpressions.ToList().Concat(expr.Witness.SubExpressions.ToList());
        foreach (var expression in functionCalls) {
          if (expression is FunctionCallExpr funcExpr) {
            var func = funcExpr.Function;

            if (isRevealedAlongPath(func, moduleDefinition, new List<ModuleDefinition> { func.EnclosingClass.EnclosingModuleDefinition })) {
              if (!func.IsOpaque && func.DoesAllOpaqueMakeOpaque(Options)) {
                var revealStmt0 = BuildRevealStmt(new FunctionReveal(func, new List<NameSegment>()), expr.Witness.Tok, moduleDefinition);

                if (revealStmt0 is not null) {
                  var newExpr = new StmtExpr(expr.Witness.Tok, revealStmt0, expr.Witness) {
                    Type = expr.Witness.Type
                  };
                  expr.Witness = newExpr;
                }
              }

              using IEnumerator<FunctionReveal> enumerator = GetEnumerator(func, func.EnclosingClass, new List<Expression>(), moduleDefinition);
              while (enumerator.MoveNext()) {
                var newFunc = enumerator.Current;
      
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
  
  internal class GraphTraversalVertex {
    public readonly Graph<ICallable>.Vertex Vertex;
    public readonly bool Local;

    public List<NameSegment> namePath;
    public List<ModuleDefinition> modulePath;

    public GraphTraversalVertex(Graph<ICallable>.Vertex vertex, bool local, List<NameSegment> namePath, List<ModuleDefinition> modulePath) {
      this.Vertex = vertex;
      this.Local = local;
      this.namePath = namePath;
      this.modulePath = modulePath;
    }

    public override bool Equals(object obj)
    {
      GraphTraversalVertex other = obj as GraphTraversalVertex;
      return other.Vertex.N.FullSanitizedName == Vertex.N.FullSanitizedName;
    }

    public override int GetHashCode()
    {
      return HashCode.Combine(Vertex.N.FullSanitizedName);
    }
  }

  private void AddMethodReveals(Method m, ErrorReporter reporter) {
    Contract.Requires(m != null);

    var currentClass = m.EnclosingClass;
    List<RevealStmt> addedReveals = new List<RevealStmt>();

    using IEnumerator<FunctionReveal> enumerator = GetEnumerator(m, currentClass, m.SubExpressions);
    while (enumerator.MoveNext())
    {
      var func = enumerator.Current;
      var revealStmt = BuildRevealStmt(func, m.Tok, m.EnclosingClass.EnclosingModuleDefinition);

      if (revealStmt is not null) {
        addedReveals.Add(revealStmt);

        if (!Attributes.Contains(m.Attributes, "allOpaque")) {
          if (m is Constructor c) {
            c.BodyInit.Insert(0, revealStmt);
          } else {
            m.Body.Body.Insert(0, revealStmt);
          }
        }
      }
    }

    if (!Attributes.Contains(m.Attributes, "allOpaque")) {
      if (m.Req.Any() || m.Ens.Any()) {
        Expression reqExpr = new LiteralExpr(m.Tok, true);
        reqExpr.Type = Type.Bool;
        foreach (var revealStmt0 in addedReveals) {
          reqExpr = new StmtExpr(reqExpr.tok, revealStmt0, reqExpr);
          reqExpr.Type = Type.Bool;
        }

        // m.Req.Add(new AttributedExpression(reqExpr));
        m.Req.Insert(0, new AttributedExpression(reqExpr));
      }
    }

    if (addedReveals.Any()) {
      reporter.Message(MessageSource.Rewriter, ErrorLevel.Info, null, m.tok, RenderedRevealStmts(addedReveals));
    }
  }

  private void AddFunctionReveals(Function f, ErrorReporter reporter) {
    Contract.Requires(f != null);

    var currentClass = f.EnclosingClass;
    List<RevealStmt> addedReveals = new List<RevealStmt>();

    using IEnumerator<FunctionReveal> enumerator = GetEnumerator(f, currentClass, f.SubExpressions);
    while (enumerator.MoveNext()) {
      var func = enumerator.Current;

      if (func.function == f) {
        continue;
      }
      
      var origExpr = f.Body;
      var revealStmt = BuildRevealStmt(func, f.Tok, f.EnclosingClass.EnclosingModuleDefinition);

      if (revealStmt is not null) {
        addedReveals.Add(revealStmt);
        
        if (!Attributes.Contains(f.Attributes, "allOpaque")) {
          var newExpr = new StmtExpr(f.Tok, revealStmt, origExpr) {
            Type = origExpr.Type
          };
          f.Body = newExpr;
        }
      }
    }

    if (!Attributes.Contains(f.Attributes, "allOpaque")) {
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
      reporter.Message(MessageSource.Rewriter, ErrorLevel.Info, null, f.tok, RenderedRevealStmts(addedReveals));
    }
  }
  
  private static string RenderedRevealStmts(List<RevealStmt> revealStmtList) {
    Contract.Requires(revealStmtList.Any());
    return revealStmtList.Aggregate("", (s, stmt) => s + " " + stmt)[1..];
  }
  
  private IEnumerator<FunctionReveal> GetEnumerator(ICallable m, TopLevelDecl currentClass, IEnumerable<Expression> subexpressions, ModuleDefinition rootModule = null) {
    var vertex = currentClass.EnclosingModuleDefinition.CallGraph.FindVertex(m);
    var interModuleVertex = currentClass.EnclosingModuleDefinition.InterModuleCallGraph.FindVertex(m);

    if (vertex is null) {
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
    
    foreach (var callable in vertex.Successors) {
      queue.Enqueue(new GraphTraversalVertex(callable, true, defaultNameSegmentPath.ToList(), defaultModulePath.ToList()));
    }

    Type[] typeList = ExprListToTypeList(subexpressions.ToArray()).ToArray();

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
      }
    );

    if (interModuleVertex is not null) {
      foreach (var callable in interModuleVertex.Successors) {

        var newModulePath = defaultModulePath.ToList();
        newModulePath.Add(callable.N.EnclosingModule);
        
        if (isRevealedAlongPath(callable.N, defaultRootModule, newModulePath)) {
          var importName = computeImportName(defaultRootModule, callable.N.EnclosingModule);
          
          if (importName is not null) {
            var newNameSegmentPath = defaultNameSegmentPath.ToList();
            newNameSegmentPath.Add(importName);
            queue.Enqueue(new GraphTraversalVertex(callable, false, newNameSegmentPath, newModulePath.ToList()));
          } else {
            queue.Enqueue(new GraphTraversalVertex(callable, false, defaultNameSegmentPath.ToList(), newModulePath.ToList()));
          }
        }
      }
    }

    while (queue.Any()) {
      var newVertex = queue.Dequeue();
      if (!visited.Contains(newVertex)) {
        visited.Add(newVertex);
        
        Graph<ICallable>.Vertex origNewVertex;
        Graph<ICallable>.Vertex newInterModuleVertex;

        if (newVertex.Local) {
          origNewVertex = newVertex.Vertex;
          
        } else {
          origNewVertex = newVertex.Vertex.N.EnclosingModule.CallGraph.FindVertex(newVertex.Vertex.N);
          
          if (origNewVertex is null) {
            continue;
          }
        }
        
        newInterModuleVertex = origNewVertex.N.EnclosingModule.InterModuleCallGraph.FindVertex(origNewVertex.N);
        
        foreach (var vertex0 in origNewVertex.Successors) {
          if (isRevealedAlongPath(vertex0.N, defaultRootModule, newVertex.modulePath)) {
            var newGraphTraversalVertex =
              new GraphTraversalVertex(vertex0, true, newVertex.namePath, newVertex.modulePath);

            if (!visited.Contains(newGraphTraversalVertex)) {
              queue.Enqueue(newGraphTraversalVertex);
            }
            
          }
        }

        if (newInterModuleVertex is not null) {
          foreach (var vertex0 in newInterModuleVertex.Successors) {
            var newNamePath = newVertex.namePath.ToList();
            var importName = computeImportName(origNewVertex.N.EnclosingModule, vertex0.N.EnclosingModule);

            if (importName is not null) {
              newNamePath.Add(importName);
            }

            var newModulePath = newVertex.modulePath.ToList();
            newModulePath.Add(vertex0.N.EnclosingModule);

            if (isRevealedAlongPath(vertex0.N, defaultRootModule, newModulePath)) {
              queue.Enqueue(new GraphTraversalVertex(vertex0, false, newNamePath, newModulePath));
            }
            
          }
        }

        var callable = origNewVertex.N;
        
        if (callable is Function { IsOpaque: false } func && func.DoesAllOpaqueMakeOpaque(Options)) {
          yield return new FunctionReveal(func, newVertex.namePath.ToList());
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
    
    for (var i=0; i < modulePathLocalCopy.Count()-1; i++) {
      var exportSet = FindModuleExportSet(modulePathLocalCopy[i + 1], modulePathLocalCopy[i]);

      // if (modulePathLocalCopy[i].IsAbstract) {
      //   
      // }
      
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
      var importedModuleName = importedMod.FullName[..^4]; //Remove .Abs at the end
      
      foreach (AbstractModuleDecl abstractModuleDecl in origMod.TopLevelDecls.Where(decl => decl is AbstractModuleDecl)) {
        if (abstractModuleDecl.FullName == importedModuleName) {
          return abstractModuleDecl.Exports.Any() ? abstractModuleDecl.Exports.First().val : importedMod.Name;
        }
      }
    }

    return importedMod.Name;
    // Reporter.Error(MessageSource.Rewriter, ErrorLevel.Error, origMod.tok, "AllOpaqueRewriter error - cannot find module import " + importedMod.Name + " in " + origMod.Name);
  }

  private NameSegment computeImportName(ModuleDefinition origModule, ModuleDefinition newModule) {
    // throw new NotImplementedException();

    foreach (AliasModuleDecl aliasModDecl in origModule.TopLevelDecls.Where(decl => decl is AliasModuleDecl)) {
      if (aliasModDecl.TargetQId.Root.FullDafnyName == newModule.FullDafnyName) {
        return new NameSegment(aliasModDecl.tok, aliasModDecl.Name, new List<Type>());
      }
    }

    if (newModule.IsAbstract) {
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
  //
  // struct TypeRevealableInfo {
  //   private Type type;
  //   private List<NameSegment> namePath;
  //   private List<ModuleDefinition> modulePath;
  // }
  
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
    
    var subSubexpressionTypeList = exprList.Select(expr => ExprListToTypeList(expr.SubExpressions));

    var subexpressionTypeList = exprList.Select(expr => expr.Type).ToArray();
    var subSubexpressionListConcat = subSubexpressionTypeList.SelectMany(x => x);
    
    return subexpressionTypeList.Concat(subSubexpressionListConcat);
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
    
    var receiver = new StaticReceiverExpr(tok, new UserDefinedType(tok, callableName, callableClass, callableClass.TypeArgs.ConvertAll(obj => (Type) Type.Int) ), callableClass, true);

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
}