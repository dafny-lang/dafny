using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny {
  /// <summary>
  /// This class builds the call graph for a resolved list of declarations.
  /// It also sets
  ///   -- the .IsRecursive, .AllCalls, and .ContainsQuantifier fields of Function,
  ///   -- the .Uses field of ExtremePredicate, and
  ///   -- the .IsRecursive and .AssignedAssumptionVariables fields of Method.
  /// It assumes that the given declarations have been resolved (name resolution and type checking).
  ///
  /// The call graph of a module is stored as a field .CallGraph in ModuleDefinition. The edges of such
  /// a call graph are between vertices of the module itself, with one exception: there can also be edges
  /// from trait members in a different module to the overriding members in the module. The methods
  /// in this CallGraphBuilder class populate the .CallGraph of modules.
  ///
  /// The public Build method adds the call-graph edges for the given declarations. It assumes
  /// that the specification of iterators have already been created, and adds call-graph edges for them, too.
  /// The Build method works with the "nested" match constructs and does not need to go into their desugarings
  /// (in fact, it's even okay if those desugarings have not yet been created--creating them later does not
  /// give rise to any new edges).
  ///
  /// A call to a function-by-method goes to the "function" part if the call is in a ghost context and goes
  /// to the "by method" part if the call is in a compiled context. The Build method does not assume ghost
  /// interests have been computed, so the edge to the "by method" part may be missing. (The edge to the
  /// "function" part is added and so is the edge from the "by method" part to the "function" part, so no
  /// edges need to be removed.) Instead, when the resolver later determines that a call goes to the "by method"
  /// part, it will call the AddCallGraphEdge method directly.
  ///
  /// Building the call graph for the "system" module (the module that contains Dafny's built-in declarations)
  /// works a little differently. It calls Build only for a subset of the top-level declarations in the
  /// system module. The other declarations are handled in the resolver's ResolveValuetypeDecls() method,
  /// which calls into the VisitFunction and VisitMethod methods below.
  ///
  /// The Build method does NOT add the edges associated with the bodies of prefix predicates/lemmas, because
  /// those bodies are not created until later in the resolution phases. The creation of those bodies uses
  /// the parts of the call graph that is built up here. After those prefix bodies have been created, the
  /// resolver calls into the VisitFunction/VisitMethod methods here to add edges for the prefix bodies.
  /// </summary>
  public class CallGraphBuilder {
    public static void Build(List<TopLevelDecl> declarations, ErrorReporter reporter) {
      var astVisitor = new CallGraphASTVisitor(new CallGraphBuilder(reporter));
      astVisitor.VisitDeclarations(declarations);
    }

    public static void VisitFunction(Function function, ErrorReporter reporter) {
      var astVisitor = new CallGraphASTVisitor(new CallGraphBuilder(reporter));
      astVisitor.VisitFunction(function);
    }

    public static void VisitMethod(Method method, ErrorReporter reporter) {
      var astVisitor = new CallGraphASTVisitor(new CallGraphBuilder(reporter));
      astVisitor.VisitMethod(method);
    }

    public static void AddCallGraphEdge(ICodeContext callingContext, ICallable function, Expression e, ErrorReporter reporter) {
      new CallGraphBuilder(reporter).AddCallGraphEdge(CodeContextWrapper.Unwrap(callingContext), function, e, false);
    }

    private readonly ErrorReporter reporter;

    /// <summary>
    /// The only reason there is a constructor for this class is to keep track of the "reporter" as an instance field.
    /// </summary>
    private CallGraphBuilder(ErrorReporter reporter) {
      this.reporter = reporter;
    }

    private class CallGraphBuilderContext {
      public readonly IASTVisitorContext CodeContext;
      public bool InFunctionPostcondition { get; init; }
      public CallGraphBuilderContext(IASTVisitorContext codeContext) {
        CodeContext = codeContext;
      }
    }

    private class CallGraphASTVisitor : ASTVisitor {
      private readonly CallGraphBuilder callGraphBuilder;
      public CallGraphASTVisitor(CallGraphBuilder callGraphBuilder) {
        this.callGraphBuilder = callGraphBuilder;
      }

      public override void VisitFunction(Function f) {
        if (f.OverriddenFunction != null) {
          // add an edge from the trait function to that of the class/type
         callGraphBuilder.AddCallGraphEdgeRaw(f.OverriddenFunction, f);
        }

        if (f is PrefixPredicate prefixPredicate) {
          // add an edge from P# to P, since this will have the desired effect of detecting unwanted cycles.
          callGraphBuilder.AddCallGraphEdgeRaw(prefixPredicate, prefixPredicate.ExtremePred);
        }

        base.VisitFunction(f);
      }

      public override void VisitMethod(Method method) {
        if (method.OverriddenMethod != null) {
          // add an edge from the trait method to that of the class/type
          callGraphBuilder.AddCallGraphEdgeRaw(method.OverriddenMethod, method);
        }

        if (method is PrefixLemma prefixLemma) {
          // add an edge from M# to M, since this will have the desired effect of detecting unwanted cycles.
          callGraphBuilder.AddCallGraphEdgeRaw(prefixLemma, prefixLemma.ExtremeLemma);
        }

        base.VisitMethod(method);
      }

      private CallGraphBuilderContext GetCallGraphBuilderContext(IASTVisitorContext context) {
        return new CallGraphBuilderContext(context) { InFunctionPostcondition = InFunctionPostcondition };
      }

      protected override void VisitUserProvidedType(Type type, IASTVisitorContext context) {
        callGraphBuilder.VisitUserProvidedType(type, GetCallGraphBuilderContext(context));
      }

      protected override void VisitExpression(Expression expr, IASTVisitorContext context) {
        callGraphBuilder.VisitExpression(expr, GetCallGraphBuilderContext(context));
      }

      protected override void VisitStatement(Statement stmt, IASTVisitorContext context) {
        callGraphBuilder.VisitStatement(stmt, GetCallGraphBuilderContext(context));
      }
    }

    /// <summary>
    /// This method, the two AddCallGraphEdge methods, and AddTypeDependencyEdges are what the
    /// CallGraphBuilder is all about. These two methods are called during the traversal of the
    /// declarations given to the public Build method.
    /// </summary>
    private void AddCallGraphEdgeForField(IASTVisitorContext callingContext, Field field, Expression e) {
      Contract.Requires(callingContext != null);
      Contract.Requires(field != null);
      Contract.Requires(e != null);
      if (field is ConstantField cf) {
        if (cf == callingContext) {
          // detect self-loops here, since they don't show up in the graph's SSC methods
          reporter.Error(MessageSource.Resolver, cf.tok, "recursive dependency involving constant initialization: {0} -> {0}", cf.Name);
        } else {
          AddCallGraphEdge(callingContext, cf, e, false);
        }
      }
    }

    /// <summary>
    /// See comment about AddCallGraphEdgeForField.
    /// </summary>
    private void AddCallGraphEdge(IASTVisitorContext callingContext, ICallable callable, Expression e, bool isFunctionReturnValue) {
      Contract.Requires(callingContext != null);
      Contract.Requires(callable != null);
      Contract.Requires(e != null);
      ModuleDefinition callerModule = callingContext.EnclosingModule;
      ModuleDefinition calleeModule = callable is SpecialFunction ? null : callable.EnclosingModule;
      if (callerModule != calleeModule) {
        // inter-module call; don't record in call graph
        return;
      }

      // intra-module call; add edge in module's call graph
      if (callingContext is ICallable caller) {
        callerModule.CallGraph.AddEdge(caller, callable);
        if (caller is Function f) {
          if (e is FunctionCallExpr ee) {
            f.AllCalls.Add(ee);
          }
          // if the call denotes the function return value in the function postconditions, then we don't
          // mark it as recursive.
          if (caller == callable && !isFunctionReturnValue) {
            f.IsRecursive = true;  // self recursion (mutual recursion is determined elsewhere)
          }
        }
      }
    }

    /// <summary>
    /// See comment about AddCallGraphEdgeForField.
    /// </summary>
    private void AddCallGraphEdge(CallStmt s, CallGraphBuilderContext context) {
      Contract.Requires(s != null);
      Contract.Requires(context != null);
      var callee = s.Method;
      ModuleDefinition callerModule = context.CodeContext.EnclosingModule;
      ModuleDefinition calleeModule = ((IASTVisitorContext)callee).EnclosingModule;
      if (callerModule != calleeModule) {
        // inter-module call; don't record in call graph
        return;
      }

      // intra-module call; add edge in module's call graph
      if (context.CodeContext is ICallable caller) {
        if (caller is IteratorDecl iteratorDecl) {
          // use the MoveNext() method as the caller
          callerModule.CallGraph.AddEdge(iteratorDecl.Member_MoveNext, callee);
        } else {
          callerModule.CallGraph.AddEdge(caller, callee);
          if (caller == callee) {
            callee.IsRecursive = true; // self recursion (mutual recursion is determined elsewhere)
          }
        }
      }
    }

    private void AddCallGraphEdgeRaw(ICallable caller, ICallable callee) {
      callee.EnclosingModule.CallGraph.AddEdge(caller, callee);
    }

    /// <summary>
    /// Add edges to the call graph.
    /// See comment about AddCallGraphEdgeForField.
    /// </summary>
    private void AddTypeDependencyEdges(IASTVisitorContext context, Type type) {
      Contract.Requires(type != null);
      Contract.Requires(context != null);
      if (context is ICallable caller && type is NonProxyType) {
        type.ForeachTypeComponent(ty => {
          if ((ty as UserDefinedType)?.ResolvedClass is ICallable cl && caller.EnclosingModule == cl.EnclosingModule) {
            caller.EnclosingModule.CallGraph.AddEdge(caller, cl);
          }
        });
      }
    }

    /// <summary>
    /// This method builds the call graph for the given declarations. It assumes that all declarations have been
    /// successfully resolved and type checked.
    /// </summary>
    private void Build(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        VisitAttributes(d, new CallGraphBuilderContext(new NoContext(d.EnclosingModuleDefinition)));

        if (d is RedirectingTypeDecl) {
          var dd = (RedirectingTypeDecl)d;
          var baseType = (d as NewtypeDecl)?.BaseType ?? ((TypeSynonymDeclBase)d).Rhs;
          VisitUserProvidedType(baseType, new CallGraphBuilderContext(dd));
          if (dd.Constraint != null) {
            VisitExpression(dd.Constraint, new CallGraphBuilderContext(dd));
          }
          if (dd.Witness != null) {
            VisitExpression(dd.Witness, new CallGraphBuilderContext(dd));
          }

        } else if (d is IteratorDecl) {
          var iter = (IteratorDecl)d;
          VisitIterator(iter);

        } else if (d is DatatypeDecl) {
          var dt = (DatatypeDecl)d;
          foreach (var ctor in dt.Ctors) {
            VisitAttributes(ctor, new CallGraphBuilderContext(new NoContext(d.EnclosingModuleDefinition)));
            foreach (var formal in ctor.Formals) {
              AddTypeDependencyEdges((ICallable)d, formal.Type);
            }
          }
          foreach (var ctor in dt.Ctors) {
            VisitDefaultParameterValues(ctor.Formals, new CallGraphBuilderContext(dt));
          }
        }

        if (d is TopLevelDeclWithMembers cl) {
          VisitClassMemberBodies(cl);
        }
      }
    }

    private void VisitAttributes(IAttributeBearingDeclaration attributeHost, CallGraphBuilderContext context) {
      foreach (var attr in attributeHost.Attributes.AsEnumerable()) {
        if (attr.Args != null) {
          foreach (var arg in attr.Args) {
            VisitExpression(arg, context);
          }
        }
      }
    }

    private void VisitClassMemberBodies(TopLevelDeclWithMembers cl) {
      Contract.Requires(cl != null);

      foreach (var member in cl.Members) {
        if (member is ConstantField constantField) {
          var context = new CallGraphBuilderContext(constantField);
          VisitAttributes(constantField, context);
          VisitUserProvidedType(constantField.Type, context);
          if (constantField.Rhs != null) {
            VisitExpression(constantField.Rhs, context);
          }
        } else if (member is Field field) {
          var context = new CallGraphBuilderContext(new NoContext(cl.EnclosingModuleDefinition));
          VisitAttributes(field, context);
          VisitUserProvidedType(field.Type, context);
        } else if (member is Function function) {
          VisitFunction(function);
        } else if (member is Method method) {
          VisitMethod(method);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected member type
        }
      }
    }

    private void VisitIterator(IteratorDecl iter) {
      Contract.Requires(iter != null);

      var context = new CallGraphBuilderContext(iter); // single-state context

      VisitAttributes(iter, context);
      VisitDefaultParameterValues(iter.Ins, context);

      VisitAttributes(iter.Decreases, context);
      for (var i = 0; i < iter.Decreases.Expressions.Count; i++) {
        var e = iter.Decreases.Expressions[i];
        VisitExpression(e, context);
      }
      foreach (FrameExpression fe in iter.Reads.Expressions) {
        VisitExpression(fe.E, new CallGraphBuilderContext(iter));
      }
      VisitAttributes(iter.Modifies, context);
      foreach (FrameExpression fe in iter.Modifies.Expressions) {
        VisitExpression(fe.E, new CallGraphBuilderContext(iter));
      }
      foreach (AttributedExpression e in iter.Requires) {
        VisitAttributes(e, context);
        VisitExpression(e.E, context);
      }

      foreach (AttributedExpression e in iter.YieldRequires) {
        VisitAttributes(e, context);
        VisitExpression(e.E, context);
      }
      foreach (AttributedExpression e in iter.YieldEnsures) {
        VisitAttributes(e, new CallGraphBuilderContext(iter));
        VisitExpression(e.E, new CallGraphBuilderContext(iter));
      }
      foreach (AttributedExpression e in iter.Ensures) {
        VisitAttributes(e, new CallGraphBuilderContext(iter));
        VisitExpression(e.E, new CallGraphBuilderContext(iter));
      }

      if (iter.Body != null) {
        VisitStatement(iter.Body, new CallGraphBuilderContext(iter));
      }
    }

    /// <summary>
    /// Visits a function and its body.
    /// </summary>
    private void VisitFunction(Function f) {
      VisitFunctionProper(f);

      var prefixPredicate = (f as ExtremePredicate)?.PrefixPredicate;
      if (prefixPredicate != null) {
        VisitFunctionProper(prefixPredicate);
      }

      if (f.ByMethodDecl != null) {
        VisitMethod(f.ByMethodDecl);
      }
    }

    private void VisitFunctionProper(Function f) {
      if (f.OverriddenFunction != null) {
        // add an edge from the trait function to that of the class/type
        AddCallGraphEdgeRaw(f.OverriddenFunction, f);
      }

      if (f is PrefixPredicate prefixPredicate) {
        // add an edge from P# to P, since this will have the desired effect of detecting unwanted cycles.
        AddCallGraphEdgeRaw(prefixPredicate, prefixPredicate.ExtremePred);
      }

      VisitAttributes(f, new CallGraphBuilderContext(f));

      foreach (var formal in f.Formals) {
        VisitUserProvidedType(formal.Type, new CallGraphBuilderContext(f));
      }
      VisitUserProvidedType(f.ResultType, new CallGraphBuilderContext(f));

      VisitDefaultParameterValues(f.Formals, new CallGraphBuilderContext(f));

      foreach (AttributedExpression e in f.Req) {
        VisitAttributes(e, new CallGraphBuilderContext(f));
        VisitExpression(e.E, new CallGraphBuilderContext(f));
      }
      foreach (FrameExpression fr in f.Reads) {
        VisitExpression(fr.E, new CallGraphBuilderContext(f));
      }
      foreach (AttributedExpression e in f.Ens) {
        VisitAttributes(e, new CallGraphBuilderContext(f));
        VisitExpression(e.E, new CallGraphBuilderContext(f) { InFunctionPostcondition = true });
      }
      VisitAttributes(f.Decreases, new CallGraphBuilderContext(f));
      foreach (Expression r in f.Decreases.Expressions) {
        VisitExpression(r, new CallGraphBuilderContext(f));
      }

      if (f.ByMethodBody != null) {
        // The following conditions are assured by the parser and other callers of the Function constructor
        Contract.Assert(f.Body != null);
        Contract.Assert(!f.IsGhost);
      }
      if (f.Body != null) {
        VisitExpression(f.Body, new CallGraphBuilderContext(f));
      }
    }

    private void VisitExpression(Expression expr, CallGraphBuilderContext context) {
      Contract.Requires(expr != null);
      Contract.Requires(context != null);

      if (expr is DefaultValueExpression) {
        // A DefaultValueExpression is a wrapper around the expression given as a default in the callee's declaration.
        // It hasn't yet been resolved, so we can't process it here. But that's okay, because we will set up the necessary
        // call graph edges when processing the callee's declaration.
        return;
      }
      expr = expr.Resolved;

      if (expr is DatatypeValue dtv) {
        var dt = dtv.Type.AsDatatype;
        if (context.CodeContext is ICallable caller && caller.EnclosingModule == dt.EnclosingModuleDefinition) {
          caller.EnclosingModule.CallGraph.AddEdge(caller, dt);
        }

      } else if (expr is MemberSelectExpr memberSelectExpr) {
        if (memberSelectExpr.Member is Function function) {
          AddCallGraphEdge(context.CodeContext, function, memberSelectExpr, false);
        } else if (memberSelectExpr.Member is Field field) {
          AddCallGraphEdgeForField(context.CodeContext, field, memberSelectExpr);
        } else {
          // Apparently, we're called on the CallStmt.MemberSelect expression. The call-graph edge is added by the
          // handling of the CallStmt. Below, we will continue visiting the MemberSelectExpr.Obj subexpression.
          Contract.Assert(memberSelectExpr.Member is Method);
        }

      } else if (expr is FunctionCallExpr functionCallExpr) {
        var function = functionCallExpr.Function;
        if (function is ExtremePredicate extremePredicate) {
          extremePredicate.Uses.Add(functionCallExpr);
        }
        AddCallGraphEdge(context.CodeContext, function, functionCallExpr,
          IsFunctionReturnValue(function, functionCallExpr.Receiver, functionCallExpr.Args, context));

      } else if (expr is SeqConstructionExpr seqConstructionExpr) {
        var userProvidedElementType = seqConstructionExpr.ExplicitElementType;
        if (userProvidedElementType != null) {
          VisitUserProvidedType(userProvidedElementType, context);
        }

      } else if (expr is TypeUnaryExpr typeUnaryExpr) {
        VisitUserProvidedType(typeUnaryExpr.ToType, context);

      } else if (expr is LetExpr letExpr) {
        foreach (var lhs in letExpr.LHSs) {
          foreach (var v in lhs.Vars) {
            VisitUserProvidedType(v.SyntacticType, context);
          }
        }

      } else if (expr is QuantifierExpr quantifierExpr) {
        Contract.Assert(quantifierExpr.SplitQuantifier == null); // No split quantifiers during resolution
        if (context.CodeContext is Function enclosingFunction) {
          enclosingFunction.ContainsQuantifier = true;
        }
        foreach (BoundVar v in quantifierExpr.BoundVars) {
          VisitUserProvidedType(v.Type, context);
        }

      } else if (expr is SetComprehension setComprehension) {
        foreach (BoundVar v in setComprehension.BoundVars) {
          VisitUserProvidedType(v.Type, context);
        }

      } else if (expr is MapComprehension mapComprehension) {
        foreach (BoundVar v in mapComprehension.BoundVars) {
          VisitUserProvidedType(v.Type, context);
        }

      } else if (expr is LambdaExpr lambdaExpr) {
        foreach (BoundVar v in lambdaExpr.BoundVars) {
          VisitUserProvidedType(v.Type, context);
        }

      } else if (expr is StmtExpr stmtExpr) {
        VisitStatement(stmtExpr.S, context);

      } else if (expr is MatchExpr matchExpr) {
        foreach (MatchCaseExpr mc in matchExpr.Cases) {
          foreach (BoundVar v in mc.Arguments) {
            VisitUserProvidedType(v.Type, context);
          }
        }
      }

      foreach (var ee in expr.SubExpressions) {
        VisitExpression(ee, context);
      }
    }

    private void VisitDefaultParameterValues(List<Formal> formals, CallGraphBuilderContext context) {
      Contract.Requires(formals != null);
      Contract.Requires(context != null);

      foreach (var formal in formals) {
        var d = formal.DefaultValue;
        if (d != null) {
          VisitExpression(d, context);
        }
      }
    }

    /// <summary>
    /// Return "true" only if the call to "fn" with arguments "receiver/args" in context "context"
    /// denotes the function result value. (If so, the call is not a recursive call, but just a
    /// way to refer to the function's result value.)
    ///
    /// If the call is in a function postcondition, it is calling itself, and the arguments match the
    /// formal parameters, then it denotes a function return value. In general, matching the actuals with
    /// formals requires verification. Here, the two are compared syntactically. Thus, this method may
    /// return "false" even in some cases where the call denotes the function's result value.
    /// </summary>
    private bool IsFunctionReturnValue(Function fn, Expression receiver, List<Expression> args, CallGraphBuilderContext context) {
      if (context.CodeContext == fn && context.InFunctionPostcondition) {
        Contract.Assert(fn.Formals.Count == args.Count);
        return
          (fn.IsStatic || receiver.Resolved is ThisExpr) &&
          Enumerable.Range(0, args.Count).All(i => (args[i].Resolved as IdentifierExpr)?.Var == fn.Formals[i]);
      }
      return false;
    }

    private void VisitMethod(Method m) {
      VisitMethodProper(m);

      var prefixLemma = (m as ExtremeLemma)?.PrefixLemma;
      if (prefixLemma != null) {
        VisitMethodProper(prefixLemma);
      }
    }

    private void VisitMethodProper(Method m) {
      Contract.Requires(m != null);

      if (m.OverriddenMethod != null) {
        // add an edge from the trait method to that of the class/type
        AddCallGraphEdgeRaw(m.OverriddenMethod, m);
      }

      if (m is PrefixLemma prefixLemma) {
        // add an edge from M# to M, since this will have the desired effect of detecting unwanted cycles.
        AddCallGraphEdgeRaw(prefixLemma, prefixLemma.ExtremeLemma);
      }

      var context = new CallGraphBuilderContext(m);

      VisitAttributes(m, context);

      foreach (var p in m.Ins) {
        VisitUserProvidedType(p.Type, context);
      }
      foreach (var p in m.Outs) {
        VisitUserProvidedType(p.Type, context);
      }

      VisitDefaultParameterValues(m.Ins, context);

      foreach (AttributedExpression e in m.Req) {
        VisitAttributes(e, context);
        VisitExpression(e.E, context);
      }

      VisitAttributes(m.Mod, context);
      foreach (FrameExpression fe in m.Mod.Expressions) {
        VisitExpression(fe.E, context);
      }
      VisitAttributes(m.Decreases, context);
      foreach (Expression e in m.Decreases.Expressions) {
        VisitExpression(e, context);
      }

      foreach (AttributedExpression e in m.Ens) {
        VisitAttributes(e, context);
        VisitExpression(e.E, context);
      }

      if (m.Body != null) {
        VisitStatement(m.Body, context);
      }
    }

    private void VisitStatement(Statement stmt, CallGraphBuilderContext context) {
      Contract.Requires(stmt != null);
      Contract.Requires(context != null);

      if (stmt is RevealStmt revealStmt) {
        foreach (var ss in revealStmt.ResolvedStatements) {
          VisitStatement(ss, context);
        }

      } else if (stmt is VarDeclStmt varDeclStmt) {
        foreach (var local in varDeclStmt.Locals) {
          VisitUserProvidedType(local.OptionalType, context);
        }

      } else if (stmt is VarDeclPattern varDeclPattern) {
        foreach (var local in varDeclPattern.LocalVars) {
          VisitUserProvidedType(local.OptionalType, context);
        }

      } else if (stmt is AssignStmt assignStmt) {
        if (assignStmt.Rhs is TypeRhs typeRhs) {
          if (typeRhs.EType != null) {
            VisitUserProvidedType(typeRhs.EType, context);
          }
        }

        // check on assumption variables
        if (context.CodeContext is Method currentMethod &&
            (assignStmt.Lhs.Resolved as IdentifierExpr)?.Var is LocalVariable localVar &&
            Attributes.Contains(localVar.Attributes, "assumption")) {
          if ((assignStmt.Rhs as ExprRhs)?.Expr is BinaryExpr binaryExpr &&
              binaryExpr.Op == BinaryExpr.Opcode.And &&
              (binaryExpr.E0.Resolved as IdentifierExpr)?.Var == localVar &&
              !currentMethod.AssignedAssumptionVariables.Contains(localVar)) {
            currentMethod.AssignedAssumptionVariables.Add(localVar);
          } else {
            reporter.Error(MessageSource.Resolver, stmt,
              $"there may be at most one assignment to an assumption variable, the RHS of which must match the expression \"{localVar.Name} && <boolean expression>\"");
          }
        }

      } else if (stmt is CallStmt callStmt) {
        AddCallGraphEdge(callStmt, context);

      } else if (stmt is OneBodyLoopStmt oneBodyLoopStmt) {
        if (oneBodyLoopStmt is ForLoopStmt forLoopStmt) {
          VisitUserProvidedType(forLoopStmt.LoopIndex.Type, context);
        }

      } else if (stmt is ForallStmt forallStmt) {
        foreach (BoundVar v in forallStmt.BoundVars) {
          VisitUserProvidedType(v.Type, context);
        }

      } else if (stmt is MatchStmt matchStmt) {
        foreach (MatchCaseStmt mc in matchStmt.Cases) {
          if (mc.Arguments != null) {
            foreach (BoundVar v in mc.Arguments) {
              VisitUserProvidedType(v.Type, context);
            }
          }
        }
      }

      foreach (var ee in stmt.SubExpressions) {
        VisitExpression(ee, context);
      }
      foreach (var ss in stmt.SubStatements) {
        VisitStatement(ss, context);
      }
    }

    private void VisitUserProvidedType(Type type, CallGraphBuilderContext context) {
      AddTypeDependencyEdges(context.CodeContext, type);
    }
  }
}
