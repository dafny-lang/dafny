using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;
using Microsoft.Boogie;

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
      if (decl is ICanAutoRevealDependencies m) {
        m.AutoRevealDependencies(this, Options, Reporter);
      }

      if (decl is TopLevelDeclWithMembers cl) {
        foreach (var member in cl.Members) {
          if (member is ICanAutoRevealDependencies mem) {
            mem.AutoRevealDependencies(this, Options, Reporter);
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

  private static string RenderRevealStmts(List<RevealStmtWithDepth> addedRevealStmtList, int depth = 1) {
    Contract.Requires(addedRevealStmtList.Any());

    var currentDepth = depth - 1;

    string result = "";

    foreach (var revealStmt in addedRevealStmtList.Where(stmt => stmt.Depth >= depth)) {
      if (revealStmt.Depth > currentDepth) {
        currentDepth = revealStmt.Depth;
        var stmtCount = addedRevealStmtList.Count(stmt => stmt.Depth == currentDepth);
        result += $"\n\n// depth {currentDepth}: {stmtCount} {(stmtCount == 1 ? "stmt" : "stmts")}\n";
      }

      result += $"{revealStmt.RevealStmt} ";


    }
    // Removing the initial `\n\n`
    return result[2..];
  }

  public static string GenerateMessage(List<RevealStmtWithDepth> addedReveals, int autoRevealDepth = Int32.MaxValue) {
    var numInsertedReveals = addedReveals.Count(stmt => stmt.Depth <= autoRevealDepth);
    var message = "";

    message +=
      $"Found {addedReveals.Count} function {(addedReveals.Count == 1 ? "dependency" : "dependencies")}.";

    message +=
      $" {numInsertedReveals} reveal {(numInsertedReveals == 1 ? "statement" : "statements")} inserted implicitly.";

    // if (numInsertedReveals < addedReveals.Count) {
    //   message += $" Remaining:\n{RenderRevealStmts(addedReveals, 1 + autoRevealDepth)}";
    // } else {
    message += $" Reveal statements:\n{RenderRevealStmts(addedReveals)}";
    // }

    return message;
  }

  public class RevealStmtWithDepth {
    public RevealStmtWithDepth(HideRevealStmt RevealStmt, int Depth) {
      this.RevealStmt = RevealStmt;
      this.Depth = Depth;
    }

    public override bool Equals(object obj) {
      var item = obj as RevealStmtWithDepth;
      return item != null && this.RevealStmt.ToString().Equals(item.RevealStmt.ToString());
    }

    public override int GetHashCode() {
      return HashCode.Combine(RevealStmt.ToString());
    }

    public HideRevealStmt RevealStmt { get; }
    public int Depth { get; }
  };

  public record FunctionWithDepth(Function Function, int Depth);

  public IEnumerable<FunctionWithDepth> GetEnumerator(ICallable m, TopLevelDecl currentClass, IEnumerable<Expression> subexpressions, ModuleDefinition rootModule = null) {
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
              new GraphTraversalVertex(vertex0, true, 1 + vertex.Depth);

            if (!visited.Contains(newGraphTraversalVertex)) {
              queue.Enqueue(newGraphTraversalVertex);
            }
          }
        }

        if (interModuleGraphVertex is not null) {
          foreach (var vertex0 in interModuleGraphVertex.Successors) {
            if (IsRevealable(defaultRootModule.AccessibleMembers, (Declaration)vertex0.N)) {
              queue.Enqueue(new GraphTraversalVertex(vertex0, false, 1 + vertex.Depth));
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

    var subExprList = exprList.SelectMany(expr => Triggers.ExprExtensions.AllSubExpressions(expr, false, false));

    var typeList = subExprList.Select(expr => expr.Type);

    return typeList;
  }

  public IEnumerable<RevealStmtWithDepth> ExprToFunctionalDependencies(Expression expr, ModuleDefinition enclosingModule) {
    var expressionList = Triggers.ExprExtensions.AllSubExpressions(expr, false, false);
    var revealStmtList = new List<RevealStmtWithDepth>();

    foreach (var expression in expressionList) {
      if (expression is FunctionCallExpr funcExpr) {
        var func = funcExpr.Function;

        if (IsRevealable(enclosingModule.AccessibleMembers, func)) {
          if (func.IsMadeImplicitlyOpaque(Options)) {

            var revealStmt0 = BuildRevealStmt(func,
              expr.Tok, enclosingModule);

            if (revealStmt0 is not null) {
              revealStmtList.Add(new RevealStmtWithDepth(revealStmt0, 1));
            }
          }

          foreach (var newFunc in GetEnumerator(func, func.EnclosingClass, new List<Expression> { expr },
                     enclosingModule)) {

            var revealStmt1 = BuildRevealStmt(newFunc.Function, expr.Tok, enclosingModule);

            if (revealStmt1 is not null) {
              revealStmtList.Add(new RevealStmtWithDepth(revealStmt1, newFunc.Depth));
            }
          }
        }
      }
    }

    revealStmtList = revealStmtList.Distinct().ToList();
    return revealStmtList;
  }

  public Expression AddRevealStmtsToExpression(Expression expr, IEnumerable<RevealStmtWithDepth> revealStmtList) {
    var finalExpr = expr;

    foreach (var revealStmt in revealStmtList) {
      var oldExpr = finalExpr;

      finalExpr = new StmtExpr(expr.Tok, revealStmt.RevealStmt, oldExpr) {
        Type = oldExpr.Type
      };
    }

    return finalExpr;
  }

  public static HideRevealStmt BuildRevealStmt(Function func, IOrigin tok, ModuleDefinition rootModule) {
    List<Type> args = new List<Type>();
    foreach (var _ in func.EnclosingClass.TypeArgs) {
      args.Add(new IntType());
    }

    AccessibleMember accessibleMember = rootModule.AccessibleMembers[func];

    var resolveExpr = ConstructExpressionFromPath(func, accessibleMember);

    var callableClass = ((TopLevelDeclWithMembers)func.EnclosingClass);

    var callableName = HideRevealStmt.RevealLemmaPrefix + func.Name;
    var member = callableClass.Members.Find(decl => decl.Name == callableName);

    Type.PushScope(callableClass.EnclosingModuleDefinition.VisibilityScope);
    var receiver = new StaticReceiverExpr(tok, new UserDefinedType(tok, callableName, callableClass, callableClass.TypeArgs.ConvertAll(obj => (Type)Type.Int)), callableClass, true);
    Type.PopScope(callableClass.EnclosingModuleDefinition.VisibilityScope);

    if (member is null) {
      return null;
    }

    callableName = ((ICallable)member).NameRelativeToModule;
    var rr = new MemberSelectExpr(func.Tok, receiver, new Name(callableName));
    rr.Type = new InferredTypeProxy();
    rr.Member = member;
    rr.TypeApplicationJustMember = new List<Type>();
    rr.TypeApplicationAtEnclosingClass = args;

    var call = new CallStmt(func.Origin, new List<Expression>(), rr, new List<ActualBinding>(),
      func.Tok);
    call.IsGhost = true;
    call.Bindings.AcceptArgumentExpressionsAsExactParameterList(new List<Expression>());

    resolveExpr.Type = new InferredTypeProxy();
    ((ConcreteSyntaxExpression)resolveExpr).ResolvedExpression = rr;

    List<Expression> expressionList = new List<Expression> {
      new ApplySuffix(tok, null,
        resolveExpr,
        new List<ActualBinding>(), Token.NoToken)
    };

    var revealStmt = new HideRevealStmt(func.Origin, expressionList, HideRevealCmd.Modes.Reveal);
    revealStmt.ResolvedStatements.Add(call);
    revealStmt.IsGhost = true;

    return revealStmt;
  }

  private static Expression ConstructExpressionFromPath(Function func, AccessibleMember accessibleMember) {

    var topLevelDeclsList = accessibleMember.AccessPath;
    var nameList = topLevelDeclsList.Where(decl => decl.Name != "_default").ToList();

    nameList.Add(new NameSegment(func.Tok, func.Name, new List<Type>()));

    Expression nameSeed = nameList[0];
    var resolveExpr = nameList.Skip(1)
    .Aggregate(nameSeed, (acc, name) => new ExprDotName(func.Tok, acc, name.NameNode, name.OptTypeArguments));

    return resolveExpr;
  }

  public static bool IsRevealable(Dictionary<Declaration, AccessibleMember> accessibleMembers,
    Declaration decl) {
    if (accessibleMembers.TryGetValue(decl, out var member)) {
      return member.IsRevealed;
    }

    return false;
  }
}