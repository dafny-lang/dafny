using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Reflection;
using JetBrains.Annotations;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.Dafny.Plugins;

namespace Microsoft.Dafny {
  /// <summary>
  /// This class builds the call graph for a resolved list of declarations.
  /// It also sets
  ///   -- the .IsRecursive, .AllCalls, and .ContainsQuantifier fields of Function,
  ///   -- the .Uses field of ExtremePredicate, and
  ///   -- the .IsRecursive and .AssignedAssumptionVariables fields of Method.
  ///
  /// The call graph of a module is stored as a field .CallGraph in ModuleDefinition. The edges of such
  /// a call graph are between vertices of the module itself, with one exception: there can also be edges
  /// from trait members in a different module to the overriding members in the module.
  ///
  /// The Build(declarations) method adds the call-graph edges for the given declarations. It is assumed
  /// that the specification of iterators have already been created, and thus call-graph edges for them will
  /// be built here. The Build method works with the "nested" match constructs and does not need to go
  /// into their desugarings (in fact, it's even okay if those desugarings have not yet been created--creating
  /// them later does not give rise to any new edges).
  ///
  /// The Build method does NOT add the edges associated with the bodies of prefix predicates/lemmas, because
  /// those bodies are not created until later in the resolution phases. The creation of those bodies uses
  /// the parts of the call graph that is built up here. After those prefix bodies have been created, the
  /// resolver calls into the VisitFunction/VisitMethod methods here to add edges for the prefix bodies.
  /// </summary>
  public class CallGraphBuilder {
    private ErrorReporter reporter;

    public CallGraphBuilder(ErrorReporter reporter) {
      this.reporter = reporter;
    }

    class CallGraphBuilderContext {
      public readonly ICodeContext CodeContext;
      public bool InFunctionPostcondition { get; set; }
      public CallGraphBuilderContext(ICodeContext codeContext) {
        CodeContext = codeContext;
      }
    }
    
    /// <summary>
    /// This method, the two AddCallGraphEdge methods, and AddTypeDependencyEdges are what the
    /// CallGraphBuilder is all about. These two methods are called during the traversal of the
    /// declarations given to the public Build method.
    /// </summary>
    private void AddCallGraphEdgeForField(ICodeContext callingContext, Field field, Expression e) {
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
    public void AddCallGraphEdge(ICodeContext callingContext, ICallable function, Expression e, bool isFunctionReturnValue) {
      Contract.Requires(callingContext != null);
      Contract.Requires(function != null);
      Contract.Requires(e != null);
      ModuleDefinition callerModule = callingContext.EnclosingModule;
      ModuleDefinition calleeModule = function is SpecialFunction ? null : function.EnclosingModule;
      if (callerModule == calleeModule) {
        // intra-module call; add edge in module's call graph
        if (CodeContextWrapper.Unwrap(callingContext) is ICallable caller) {
          callerModule.CallGraph.AddEdge(caller, function);
          if (caller is Function f) {
            if (e is FunctionCallExpr ee) {
              f.AllCalls.Add(ee);
            }
            // if the call denotes the function return value in the function postconditions, then we don't
            // mark it as recursive.
            if (caller == function && !isFunctionReturnValue) {
              f.IsRecursive = true;  // self recursion (mutual recursion is determined elsewhere)
            }
          }
        }
      }
    }

    /// <summary>
    /// See comment about AddCallGraphEdgeForField.
    /// </summary>
    void AddCallGraphEdge(CallStmt s, CallGraphBuilderContext context) {
      Contract.Requires(s != null);
      Contract.Requires(context != null);
      var callee = s.Method;
      ModuleDefinition callerModule = context.CodeContext.EnclosingModule;
      ModuleDefinition calleeModule = ((ICodeContext)callee).EnclosingModule;
      if (callerModule == calleeModule) {
        // intra-module call; add edge in module's call graph
        if (CodeContextWrapper.Unwrap(context.CodeContext) is ICallable caller) {
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
    }

    void AddCallGraphEdgeRaw(ICallable caller, ICallable callee) {
      callee.EnclosingModule.CallGraph.AddEdge(caller, callee);
    }

    /// <summary>
    /// Add edges to the callgraph.
    /// See comment about AddCallGraphEdgeForField.
    /// </summary>
    private void AddTypeDependencyEdges(ICodeContext context, Type type) {
      Contract.Requires(type != null);
      Contract.Requires(context != null);
      if (CodeContextWrapper.Unwrap(context) is ICallable caller && type is NonProxyType) {
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
    public void Build(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        VisitAttributes(d, new CallGraphBuilderContext(new NoContext(d.EnclosingModuleDefinition)));

        if (d is RedirectingTypeDecl) {
          var dd = (RedirectingTypeDecl)d;
          var baseType = (d as NewtypeDecl)?.BaseType ?? ((TypeSynonymDeclBase)d).Rhs;
          VisitUserProvidedType(baseType, new CallGraphBuilderContext(dd));
          if (dd.Constraint != null) {
            VisitExpression(dd.Constraint, new CallGraphBuilderContext(new CodeContextWrapper(dd, true)));
          }
          if (dd.Witness != null) {
            var codeContext = new CodeContextWrapper(dd, dd.WitnessKind == SubsetTypeDecl.WKind.Ghost);
            VisitExpression(dd.Witness, new CallGraphBuilderContext(codeContext));
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
          // resolve any default parameters
          foreach (var ctor in dt.Ctors) {
            ResolveParameterDefaultValues(ctor.Formals, new CallGraphBuilderContext(dt));
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

    void VisitClassMemberBodies(TopLevelDeclWithMembers cl) {
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

    void VisitIterator(IteratorDecl iter) {
      Contract.Requires(iter != null);

      var context = new CallGraphBuilderContext(iter); // single-state context

      VisitAttributes(iter, context);
      ResolveParameterDefaultValues(iter.Ins, context);

      VisitAttributes(iter.Decreases, context);
      for (var i = 0; i < iter.Decreases.Expressions.Count; i++) {
        var e = iter.Decreases.Expressions[i];
        VisitExpression(e, context);
      }
      foreach (FrameExpression fe in iter.Reads.Expressions) {
        ResolveFrameExpressionTopLevel(fe, iter);
      }
      VisitAttributes(iter.Modifies, context);
      foreach (FrameExpression fe in iter.Modifies.Expressions) {
        ResolveFrameExpressionTopLevel(fe, iter);
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

      // Resolve body
      if (iter.Body != null) {
        ResolveBlockStatement(iter.Body, new CallGraphBuilderContext(iter));
      }
    }

    /// <summary>
    /// Visits a function and its body.
    /// </summary>
    public void VisitFunction(Function f) {
      VisitFunctionProper(f);

      if (f.OverriddenFunction != null) {
        // add an edge from the trait function to that of the class/type
        AddCallGraphEdgeRaw(f.OverriddenFunction, f);
      }

      var prefixPredicate = (f as ExtremePredicate)?.PrefixPredicate;
      if (prefixPredicate != null) {
        // add an edge from P# to P, since this will have the desired effect of detecting unwanted cycles.
        AddCallGraphEdgeRaw(prefixPredicate, f);
        VisitFunctionProper(prefixPredicate);
      }

      if (f.ByMethodDecl != null) {
        VisitMethod(f.ByMethodDecl);
      }
    }

    public void VisitFunctionProper(Function f) {
      VisitAttributes(f, new CallGraphBuilderContext(f));

      foreach (var formal in f.Formals) {
        VisitUserProvidedType(formal.Type, new CallGraphBuilderContext(f));
      }
      VisitUserProvidedType(f.ResultType, new CallGraphBuilderContext(f));

      ResolveParameterDefaultValues(f.Formals, new CallGraphBuilderContext(f));

      foreach (AttributedExpression e in f.Req) {
        VisitAttributes(e, new CallGraphBuilderContext(f));
        VisitExpression(e.E, new CallGraphBuilderContext(f));
      }
      foreach (FrameExpression fr in f.Reads) {
        ResolveFrameExpressionTopLevel(fr, f);
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

    void VisitExpression(Expression expr, CallGraphBuilderContext context) {
      Contract.Requires(expr != null);
      Contract.Requires(context != null);

      if (expr is DefaultValueExpression) {
        // A DefaultValueExpression is a wrapper around the expression given as a default in the callee's declaration.
        // It hasn't yet been resolved, so we can't process it here. But that's okay, because we will set up the necessary
        // call graph edges when processing the callee's declaration.
        return;
      }
      expr = expr.Resolved;

      if (expr is LiteralExpr) {

      } else if (expr is ThisExpr) {

      } else if (expr is IdentifierExpr) {

      } else if (expr is NegationExpression) {
        // A NegationExpression is a ConcreteSyntaxExpr, but its .ResolvedExpression may not
        // yet have been filled in--it's filled in during a later resolution phase. So, we
        // handle it here.
        var e = (NegationExpression)expr;
        VisitExpression(e.E, context);

      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        ResolveDatatypeValue(context, dtv, dtv.Type.AsDatatype, null);

      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        foreach (Expression ee in e.Elements) {
          VisitExpression(ee, context);
        }

      } else if (expr is MapDisplayExpr) {
        MapDisplayExpr e = (MapDisplayExpr)expr;
        foreach (ExpressionPair p in e.Elements) {
          VisitExpression(p.A, context);
          VisitExpression(p.B, context);
        }

      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        VisitExpression(e.Obj, context);
        if (e.Member is Function fn) {
          AddCallGraphEdge(context.CodeContext, fn, e, false);
        } else {
          var field = (Field)e.Member;
          AddCallGraphEdgeForField(context.CodeContext, field, e);
        }

      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        VisitExpression(e.Seq, context);
        if (e.E0 != null) {
          VisitExpression(e.E0, context);
        }
        if (e.E1 != null) {
          VisitExpression(e.E1, context);
        }

      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;

        VisitExpression(e.Array, context);
        foreach (Expression idx in e.Indices) {
          VisitExpression(idx, context);
        }

      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        VisitExpression(e.Seq, context);
        VisitExpression(e.Index, context);
        VisitExpression(e.Value, context);

      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        ResolveFunctionCallExpr(e, context);

      } else if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        VisitExpression(e.Function, context);
        foreach (var arg in e.Args) {
          VisitExpression(arg, context);
        }

      } else if (expr is SeqConstructionExpr) {
        var e = (SeqConstructionExpr)expr;
        VisitUserProvidedType(e.ExplicitElementType ?? new InferredTypeProxy(), context);
        VisitExpression(e.N, context);
        VisitExpression(e.Initializer, context);

      } else if (expr is MultiSetFormingExpr) {
        MultiSetFormingExpr e = (MultiSetFormingExpr)expr;
        VisitExpression(e.E, context);

      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        VisitExpression(e.E, new CallGraphBuilderContext(context.CodeContext));

      } else if (expr is UnchangedExpr) {
        var e = (UnchangedExpr)expr;
        foreach (var fe in e.Frame) {
          ResolveFrameExpression(fe, context);
        }

      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        VisitExpression(e.E, context);

      } else if (expr is TypeUnaryExpr) {
        var e = (TypeUnaryExpr)expr;
        VisitExpression(e.E, context);
        VisitUserProvidedType(e.ToType, context);

      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        VisitExpression(e.E0, context);
        VisitExpression(e.E1, context);

      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        VisitExpression(e.E0, context);
        VisitExpression(e.E1, context);
        VisitExpression(e.E2, context);

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        if (e.Exact) {
          foreach (var rhs in e.RHSs) {
            VisitExpression(rhs, context);
          }
          var i = 0;
          foreach (var lhs in e.LHSs) {
            var rhsType = i < e.RHSs.Count ? e.RHSs[i].Type : new InferredTypeProxy();
            ResolveCasePattern(lhs, context);
            // Check for duplicate names now, because not until after resolving the case pattern do we know if identifiers inside it refer to bound variables or nullary constructors
            i++;
          }
        } else {
          // let-such-that expression
          foreach (var lhs in e.LHSs) {
            var v = lhs.Var;
            VisitUserProvidedType(v.Type, context);
          }
          foreach (var rhs in e.RHSs) {
            VisitExpression(rhs, context);
          }
        }
        VisitExpression(e.Body, context);
        VisitAttributes(e, context);
      } else if (expr is QuantifierExpr) {
        var e = (QuantifierExpr)expr;
        if (context.CodeContext is Function) {
          ((Function)context.CodeContext).ContainsQuantifier = true;
        }
        Contract.Assert(e.SplitQuantifier == null); // No split quantifiers during resolution
        foreach (BoundVar v in e.BoundVars) {
          VisitUserProvidedType(v.Type, context);
        }
        if (e.Range != null) {
          VisitExpression(e.Range, context);
        }
        VisitExpression(e.Term, context);
        VisitAttributes(e, context);

      } else if (expr is SetComprehension) {
        var e = (SetComprehension)expr;
        foreach (BoundVar v in e.BoundVars) {
          VisitUserProvidedType(v.Type, context);
        }
        VisitExpression(e.Range, context);
        VisitExpression(e.Term, context);
        VisitAttributes(e, context);

      } else if (expr is MapComprehension) {
        var e = (MapComprehension)expr;
        foreach (BoundVar v in e.BoundVars) {
          VisitUserProvidedType(v.Type, context);
        }
        VisitExpression(e.Range, context);
        if (e.TermLeft != null) {
          VisitExpression(e.TermLeft, context);
        }
        VisitExpression(e.Term, context);

        VisitAttributes(e, context);

      } else if (expr is LambdaExpr) {
        var e = (LambdaExpr)expr;
        foreach (BoundVar v in e.BoundVars) {
          VisitUserProvidedType(v.Type, context);
        }

        if (e.Range != null) {
          VisitExpression(e.Range, context);
        }
        foreach (var read in e.Reads) {
          ResolveFrameExpression(read, context);
        }
        VisitExpression(e.Term, context);

      } else if (expr is WildcardExpr) {
      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        ResolveStatement(e.S, context);
        VisitExpression(e.E, context);

      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        VisitExpression(e.Test, context);
        VisitExpression(e.Thn, context);
        VisitExpression(e.Els, context);

      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        VisitExpression(e.Source, context);
        foreach (MatchCaseExpr mc in e.Cases) {
          if (mc.Arguments != null) {
            foreach (BoundVar v in mc.Arguments) {
              VisitUserProvidedType(v.Type, context);
            }
          }
          VisitExpression(mc.Body, context);
        }

      } else {
        Contract.Assert(false);
        throw new cce.UnreachableException(); // unexpected expression
      }
    }

    private void ResolveDatatypeValue(CallGraphBuilderContext context, DatatypeValue dtv, DatatypeDecl dt, Type ty, bool complain = true) {
      Contract.Requires(context != null);
      Contract.Requires(dtv != null);
      Contract.Requires(dt != null);
      Contract.Requires(ty == null || (ty.AsDatatype == dt && ty.TypeArgs.Count == dt.TypeArgs.Count));

      dtv.Bindings.Arguments.ForEach(arg => VisitExpression(arg, context));

      if (CodeContextWrapper.Unwrap(context.CodeContext) is ICallable caller && caller.EnclosingModule == dt.EnclosingModuleDefinition) {
        caller.EnclosingModule.CallGraph.AddEdge(caller, dt);
      }
    }

    void ResolveFunctionCallExpr(FunctionCallExpr e, CallGraphBuilderContext context) {
      VisitExpression(e.Receiver, context);

      var function = e.Function;
      if (function is ExtremePredicate extremePredicate) {
        extremePredicate.Uses.Add(e);
      }

      // type check the arguments
      e.Bindings.Arguments.ForEach(arg => VisitExpression(arg, context));

      AddCallGraphEdge(context.CodeContext, function, e, IsFunctionReturnValue(function, e.Receiver, e.Bindings.Arguments, context));
    }

    void ResolveFrameExpressionTopLevel(FrameExpression fe, ICodeContext codeContext) {
      ResolveFrameExpression(fe, new CallGraphBuilderContext(codeContext));
    }

    void ResolveFrameExpression(FrameExpression fe, CallGraphBuilderContext context) {
      Contract.Requires(fe != null);
      Contract.Requires(context != null);

      VisitExpression(fe.E, context);
    }

    void ResolveParameterDefaultValues(List<Formal> formals, CallGraphBuilderContext context) {
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

    public void VisitMethod(Method m) {
      VisitMethodProper(m);

      if (m.OverriddenMethod != null) {
        // add an edge from the trait method to that of the class/type
        AddCallGraphEdgeRaw(m.OverriddenMethod, m);
      }

      var prefixLemma = (m as ExtremeLemma)?.PrefixLemma;
      if (prefixLemma != null) {
        // add an edge from M# to M, since this will have the desired effect of detecting unwanted cycles.
        AddCallGraphEdgeRaw(prefixLemma, m);
        VisitMethodProper(prefixLemma);
      }
    }

    public void VisitMethodProper(Method m) {
      Contract.Requires(m != null);

      foreach (var p in m.Ins) {
        VisitUserProvidedType(p.Type, new CallGraphBuilderContext(m));
      }
      foreach (var p in m.Outs) {
        VisitUserProvidedType(p.Type, new CallGraphBuilderContext(m));
      }

      // Add in-parameters to the scope, but don't care about any duplication errors, since they have already been reported
      ResolveParameterDefaultValues(m.Ins, new CallGraphBuilderContext(m));

      // Start resolving specification...
      foreach (AttributedExpression e in m.Req) {
        VisitAttributes(e, new CallGraphBuilderContext(m));
        VisitExpression(e.E, new CallGraphBuilderContext(m));
      }

      VisitAttributes(m.Mod, new CallGraphBuilderContext(m));
      foreach (FrameExpression fe in m.Mod.Expressions) {
        ResolveFrameExpressionTopLevel(fe, m);
      }
      VisitAttributes(m.Decreases, new CallGraphBuilderContext(m));
      foreach (Expression e in m.Decreases.Expressions) {
        VisitExpression(e, new CallGraphBuilderContext(m));
      }

      // ... continue resolving specification
      foreach (AttributedExpression e in m.Ens) {
        VisitAttributes(e, new CallGraphBuilderContext(m));
        VisitExpression(e.E, new CallGraphBuilderContext(m));
      }

      // Resolve body
      if (m.Body != null) {
        ResolveBlockStatement(m.Body, new CallGraphBuilderContext(m));
      }

      // attributes are allowed to mention both in- and out-parameters (including the implicit _k, for greatest lemmas)
      VisitAttributes(m, new CallGraphBuilderContext(m));
    }

    void ResolveBlockStatement(BlockStmt blockStmt, CallGraphBuilderContext context) {
      Contract.Requires(blockStmt != null);
      Contract.Requires(context != null);

      if (blockStmt is DividedBlockStmt) {
        var div = (DividedBlockStmt)blockStmt;
        ResolveStatementList(div.BodyInit, context);
        ResolveStatementList(div.BodyProper, context);
      } else {
        ResolveStatementList(blockStmt.Body, context);
      }
    }

    void ResolveStatementList(List<Statement> statements, CallGraphBuilderContext context) {
      foreach (var stmt in statements) {
        ResolveStatementWithLabels(stmt, context);
      }
    }

    void ResolveStatementWithLabels(Statement stmt, CallGraphBuilderContext context) {
      Contract.Requires(stmt != null);
      Contract.Requires(context != null);

      ResolveStatement(stmt, context);
    }

    void ResolveStatement(Statement stmt, CallGraphBuilderContext context) {
      Contract.Requires(stmt != null);
      Contract.Requires(context != null);

      if (stmt is PredicateStmt) {
        PredicateStmt s = (PredicateStmt)stmt;
        VisitExpression(s.Expr, context);
        if (stmt is AssertStmt assertStmt && assertStmt.Proof != null) {
          ResolveStatement(assertStmt.Proof, context);
        }
        if (stmt is ExpectStmt expectStmt) {
          VisitExpression(expectStmt.Message, context);
        }

      } else if (stmt is PrintStmt) {
        var s = (PrintStmt)stmt;
        s.Args.Iter(e => VisitExpression(e, context));

      } else if (stmt is RevealStmt) {
        var s = (RevealStmt)stmt;
        ResolveStatementList(s.ResolvedStatements, context);

      } else if (stmt is BreakStmt) {

      } else if (stmt is ProduceStmt) {
        var kind = stmt is YieldStmt ? "yield" : "return";
        var s = (ProduceStmt)stmt;
        if (s.HiddenUpdate != null) {
          ResolveStatement(s.HiddenUpdate, context);
        }

      } else if (stmt is ConcreteUpdateStatement) {
        ResolveConcreteUpdateStmt((ConcreteUpdateStatement)stmt, context);

      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        // We have four cases.
        Contract.Assert(s.Update == null || s.Update is AssignSuchThatStmt || s.Update is UpdateStmt || s.Update is AssignOrReturnStmt);
        foreach (var local in s.Locals) {
          VisitUserProvidedType(local.OptionalType, context);
        }

        foreach (var local in s.Locals) {
          VisitAttributes(local, context);
        }

        if (s.Update != null) {
          ResolveConcreteUpdateStmt(s.Update, context);
        }

      } else if (stmt is VarDeclPattern) {
        VarDeclPattern s = (VarDeclPattern)stmt;
        foreach (var local in s.LocalVars) {
          VisitUserProvidedType(local.OptionalType, context);
        }
        VisitExpression(s.RHS, context);
        ResolveCasePattern(s.LHS, context);
        // Check for duplicate names now, because not until after resolving the case pattern do we know if identifiers inside it refer to bound variables or nullary constructors

      } else if (stmt is AssignStmt) {
        AssignStmt s = (AssignStmt)stmt;
        VisitExpression(s.Lhs, context);  // allow ghosts for now, tighted up below

        // check on assumption variables
        if (context.CodeContext is Method currentMethod &&
            (s.Lhs.Resolved as IdentifierExpr)?.Var is LocalVariable localVar &&
            Attributes.Contains(localVar.Attributes, "assumption")) {
          if ((s.Rhs as ExprRhs)?.Expr is BinaryExpr binaryExpr &&
              binaryExpr.Op == BinaryExpr.Opcode.And &&
              (binaryExpr.E0.Resolved as IdentifierExpr)?.Var == localVar &&
              !currentMethod.AssignedAssumptionVariables.Contains(localVar)) {
            currentMethod.AssignedAssumptionVariables.Add(localVar);
          } else {
            reporter.Error(MessageSource.Resolver, stmt,
              $"there may be at most one assignment to an assumption variable, the RHS of which must match the expression \"{localVar.Name} && <boolean expression>\"");
          }
        }

        Type lhsType = s.Lhs.Type;
        if (s.Rhs is ExprRhs) {
          ExprRhs rr = (ExprRhs)s.Rhs;
          VisitExpression(rr.Expr, context);
        } else if (s.Rhs is TypeRhs) {
          TypeRhs rr = (TypeRhs)s.Rhs;
          ResolveTypeRhs(rr, stmt, context);
        } else if (s.Rhs is HavocRhs) {
          // nothing else to do
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected RHS
        }

      } else if (stmt is CallStmt) {
        CallStmt s = (CallStmt)stmt;
        AddCallGraphEdge(s, context);
        VisitExpression(s.Receiver, context);
        s.Bindings.Arguments.ForEach(arg => VisitExpression(arg, context));

      } else if (stmt is BlockStmt) {
        var s = (BlockStmt)stmt;
        ResolveBlockStatement(s, context);

      } else if (stmt is IfStmt) {
        IfStmt s = (IfStmt)stmt;
        if (s.Guard != null) {
          VisitExpression(s.Guard, context);
        }

        ResolveBlockStatement(s.Thn, context);

        if (s.Els != null) {
          ResolveStatement(s.Els, context);
        }

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        ResolveAlternatives(s.Alternatives, null, context);

      } else if (stmt is OneBodyLoopStmt) {
        var s = (OneBodyLoopStmt)stmt;
        if (s is WhileStmt whileS && whileS.Guard != null) {
          VisitExpression(whileS.Guard, context);
        } else if (s is ForLoopStmt forS) {
          var loopIndex = forS.LoopIndex;
          VisitUserProvidedType(loopIndex.Type, context);

          VisitExpression(forS.Start, context);
          if (forS.End != null) {
            VisitExpression(forS.End, context);
          }
        }

        ResolveLoopSpecificationComponents(s.Invariants, s.Decreases, s.Mod, context);

        if (s.Body != null) {
          ResolveStatement(s.Body, context);
        }

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        ResolveAlternatives(s.Alternatives, s, context);
        ResolveLoopSpecificationComponents(s.Invariants, s.Decreases, s.Mod, context);

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;

        foreach (BoundVar v in s.BoundVars) {
          VisitUserProvidedType(v.Type, context);
        }
        VisitExpression(s.Range, context);
        foreach (var ens in s.Ens) {
          VisitExpression(ens.E, context);
        }

        if (s.Body != null) {
          ResolveStatement(s.Body, context);
        }

        if (s.ForallExpressions != null) {
          foreach (Expression expr in s.ForallExpressions) {
            VisitExpression(expr, context);
          }
        }

      } else if (stmt is ModifyStmt) {
        var s = (ModifyStmt)stmt;
        VisitAttributes(s.Mod, context);
        foreach (FrameExpression fe in s.Mod.Expressions) {
          ResolveFrameExpression(fe, context);
        }
        if (s.Body != null) {
          ResolveBlockStatement(s.Body, context);
        }

      } else if (stmt is CalcStmt) {
        CalcStmt s = (CalcStmt)stmt;

        foreach (var line in s.Lines) {
          VisitExpression(line, context);
        }

        foreach (var h in s.Hints) {
          ResolveStatementList(h.Body, context);
        }

      } else if (stmt is MatchStmt) {
        ResolveMatchStmt((MatchStmt)stmt, context);

      } else if (stmt is SkeletonStatement) {
        var s = (SkeletonStatement)stmt;
        if (s.S != null) {
          ResolveStatement(s.S, context);
        }

      } else if (stmt is ConcreteSyntaxStatement) {
        var s = (ConcreteSyntaxStatement)stmt;
        ResolveStatement(s.ResolvedStatement, context);

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    private void ResolveConcreteUpdateStmt(ConcreteUpdateStatement s, CallGraphBuilderContext context) {
      Contract.Requires(context != null);

      var lhsNameSet = new HashSet<string>();  // used to check for duplicate identifiers on the left (full duplication checking for references and the like is done during verification)
      foreach (var lhs in s.Lhss) {
        VisitExpression(lhs, context);
      }

      // RHSs
      if (s is AssignSuchThatStmt assignSuchThatStmt) {
        VisitExpression(assignSuchThatStmt.Expr, context);
      } else if (s is UpdateStmt updateStatement) {
        ResolveStatementList(updateStatement.ResolvedStatements, context);
      } else if (s is AssignOrReturnStmt assignOrReturnStmt) {
        ResolveStatementList(assignOrReturnStmt.ResolvedStatements, context);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
      VisitAttributes(s, context);
    }

    void ResolveTypeRhs(TypeRhs rr, Statement stmt, CallGraphBuilderContext context) {
      Contract.Requires(rr != null);
      Contract.Requires(stmt != null);
      Contract.Requires(context != null);
      Contract.Ensures(Contract.Result<Type>() != null);

      if (rr.ArrayDimensions != null) {
        // ---------- new T[EE]    OR    new T[EE] (elementInit)
        Contract.Assert(rr.Bindings == null && rr.Path == null && rr.InitCall == null);
        VisitUserProvidedType(rr.EType, context);
        foreach (Expression dim in rr.ArrayDimensions) {
          Contract.Assert(dim != null);
          VisitExpression(dim, context);
        }
        if (rr.ElementInit != null) {
          VisitExpression(rr.ElementInit, context);
        } else if (rr.InitDisplay != null) {
          foreach (var v in rr.InitDisplay) {
            VisitExpression(v, context);
          }
        }
      } else {
        if (rr.Bindings == null) {
          VisitUserProvidedType(rr.EType, context);
        } else {
          // ---------- new C.Init(EE)
          ResolveStatement(rr.InitCall, context);
        }
      }
    }

    void ResolveAlternatives(List<GuardedAlternative> alternatives, AlternativeLoopStmt loopToCatchBreaks, CallGraphBuilderContext context) {
      Contract.Requires(alternatives != null);
      Contract.Requires(context != null);

      // first, resolve the guards
      foreach (var alternative in alternatives) {
        VisitExpression(alternative.Guard, context);
      }

      foreach (var alternative in alternatives) {
        VisitAttributes(alternative, context);
        ResolveStatementList(alternative.Body, context);
      }
    }

    private void ResolveLoopSpecificationComponents(List<AttributedExpression> invariants, Specification<Expression> decreases,
      Specification<FrameExpression> modifies, CallGraphBuilderContext context) {
      Contract.Requires(invariants != null);
      Contract.Requires(decreases != null);
      Contract.Requires(modifies != null);
      Contract.Requires(context != null);

      foreach (AttributedExpression inv in invariants) {
        VisitAttributes(inv, context);
        VisitExpression(inv.E, context);
      }

      VisitAttributes(decreases, context);
      foreach (Expression e in decreases.Expressions) {
        VisitExpression(e, context);
      }

      VisitAttributes(modifies, context);
      if (modifies.Expressions != null) {
        foreach (FrameExpression fe in modifies.Expressions) {
          ResolveFrameExpression(fe, context);
        }
      }
    }

    void ResolveMatchStmt(MatchStmt s, CallGraphBuilderContext context) {
      Contract.Requires(s != null);
      Contract.Requires(context != null);
      Contract.Requires(s.OrigUnresolved == null);

      VisitExpression(s.Source, context);
      foreach (MatchCaseStmt mc in s.Cases) {
        if (mc.Arguments != null) {
          foreach (BoundVar v in mc.Arguments) {
            VisitUserProvidedType(v.Type, context);
          }
        }
        ResolveStatementList(mc.Body, context);
      }
    }

    void ResolveCasePattern<VT>(CasePattern<VT> pat, CallGraphBuilderContext context) where VT : IVariable {
      Contract.Requires(pat != null);
      Contract.Requires(context != null);

      if (pat.Var != null) {
        VisitUserProvidedType(pat.Var.Type, context);
        return;
      }
      var j = 0;
      if (pat.Arguments != null) {
        foreach (var arg in pat.Arguments) {
          var formal = pat.Ctor.Formals[j];
          ResolveCasePattern(arg, context);
          j++;
        }
      }
    }

    void VisitUserProvidedType(Type type, CallGraphBuilderContext context) {
      AddTypeDependencyEdges(context.CodeContext, type);
    }
  }
}
