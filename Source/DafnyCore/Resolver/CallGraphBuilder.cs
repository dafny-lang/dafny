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
  ///   -- the .IsRecursive field of Method.
  ///
  /// Note: There are other things going on, too:
  ///   -- CheckIsConstantExpr
  ///   -- CreateIteratorMethodSpecs
  ///   -- AssignedAssumptionVariables
  ///   -- "new allocation not supported in aggregate assignments" error
  /// We need to decide whether to keep these in the name resolution / type checking phase, or do them
  /// here, or do them in a separate pass.
  /// </summary>
  public class CallGraphBuilder {
    private ErrorReporter reporter;
    TopLevelDeclWithMembers currentClass; // TODO: is this really needed in CallGraphBuilder?

    public CallGraphBuilder(ErrorReporter reporter) {
      this.reporter = reporter;
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
    void AddCallGraphEdge(CallStmt s, ResolutionContext resolutionContext) {
      Contract.Requires(s != null);
      Contract.Requires(resolutionContext != null);
      var callee = s.Method;
      ModuleDefinition callerModule = resolutionContext.CodeContext.EnclosingModule;
      ModuleDefinition calleeModule = ((ICodeContext)callee).EnclosingModule;
      if (callerModule == calleeModule) {
        // intra-module call; add edge in module's call graph
        if (CodeContextWrapper.Unwrap(resolutionContext.CodeContext) is ICallable caller) {
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
        VisitAttributes(d, ResolutionContext.FromCodeContext(new NoContext(d.EnclosingModuleDefinition)));

        if (d is RedirectingTypeDecl) {
          var dd = (RedirectingTypeDecl)d;
          var baseType = (d as NewtypeDecl)?.BaseType ?? ((TypeSynonymDeclBase)d).Rhs;
          VisitUserProvidedType(baseType, ResolutionContext.FromCodeContext(dd));
          if (dd.Constraint != null) {
            VisitExpression(dd.Constraint, new ResolutionContext(new CodeContextWrapper(dd, true), false));
          }
          if (dd.Witness != null) {
            var codeContext = new CodeContextWrapper(dd, dd.WitnessKind == SubsetTypeDecl.WKind.Ghost);
            VisitExpression(dd.Witness, new ResolutionContext(codeContext, false));
          }

        } else if (d is IteratorDecl) {
          var iter = (IteratorDecl)d;
          VisitIterator(iter);

        } else if (d is DatatypeDecl) {
          var dt = (DatatypeDecl)d;
          foreach (var ctor in dt.Ctors) {
            VisitAttributes(ctor, ResolutionContext.FromCodeContext(new NoContext(d.EnclosingModuleDefinition)));
            foreach (var formal in ctor.Formals) {
              AddTypeDependencyEdges((ICallable)d, formal.Type);
            }
          }
          // resolve any default parameters
          foreach (var ctor in dt.Ctors) {
            ResolveParameterDefaultValues(ctor.Formals, ResolutionContext.FromCodeContext(dt));
          }
        }

        if (d is TopLevelDeclWithMembers cl) {
          VisitClassMemberBodies(cl);
        }
      }
    }

    private void VisitAttributes(IAttributeBearingDeclaration attributeHost, ResolutionContext resolutionContext) {
      foreach (var attr in attributeHost.Attributes.AsEnumerable()) {
        if (attr.Args != null) {
          foreach (var arg in attr.Args) {
            VisitExpression(arg, resolutionContext);
          }
        }
      }
    }

    void VisitClassMemberBodies(TopLevelDeclWithMembers cl) {
      Contract.Requires(cl != null);
      Contract.Requires(currentClass == null);
      Contract.Ensures(currentClass == null);

      currentClass = cl;
      foreach (var member in cl.Members) {
        if (member is ConstantField constantField) {
          var resolutionContext = ResolutionContext.FromCodeContext(constantField);
          VisitAttributes(constantField, resolutionContext);
          VisitUserProvidedType(constantField.Type, resolutionContext);
          if (constantField.Rhs != null) {
            VisitExpression(constantField.Rhs, resolutionContext);
            CheckIsConstantExpr(constantField, constantField.Rhs);
          }
        } else if (member is Field field) {
          var resolutionContext = ResolutionContext.FromCodeContext(new NoContext(cl.EnclosingModuleDefinition));
          VisitAttributes(field, resolutionContext);
          VisitUserProvidedType(field.Type, resolutionContext);
        } else if (member is Function function) {
          VisitFunction(function);
        } else if (member is Method method) {
          VisitMethod(method);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected member type
        }
      }
      currentClass = null;
    }

    /// <summary>
    /// Checks if "expr" is a constant (that is, heap independent) expression that can be assigned to "field".
    /// If it is, return "true". Otherwise, report an error and return "false".
    /// This method also adds dependency edges to the module's call graph.
    /// </summary>
    void CheckIsConstantExpr(ConstantField field, Expression expr) {
      Contract.Requires(field != null);
      Contract.Requires(expr != null);
      if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        if (e.Member is Field && ((Field)e.Member).IsMutable) {
          reporter.Error(MessageSource.Resolver, field.tok, "only constants are allowed in the expression to initialize constant {0}", field.Name);
        }
        if (e.Member is ICallable other && field.EnclosingModule == other.EnclosingModule) {
          field.EnclosingModule.CallGraph.AddEdge(field, other);
        }
        // okay so far; now, go on checking subexpressions
      }
      expr.SubExpressions.Iter(e => CheckIsConstantExpr(field, e));
    }

    void VisitIterator(IteratorDecl iter) {
      Contract.Requires(iter != null);
      Contract.Requires(currentClass == null);
      Contract.Ensures(currentClass == null);

      var resolutionContext = new ResolutionContext(iter, false); // single-state context

      VisitAttributes(iter, resolutionContext);
      ResolveParameterDefaultValues(iter.Ins, resolutionContext);

      VisitAttributes(iter.Decreases, resolutionContext);
      for (var i = 0; i < iter.Decreases.Expressions.Count; i++) {
        var e = iter.Decreases.Expressions[i];
        VisitExpression(e, resolutionContext);
      }
      foreach (FrameExpression fe in iter.Reads.Expressions) {
        ResolveFrameExpressionTopLevel(fe, iter);
      }
      VisitAttributes(iter.Modifies, resolutionContext);
      foreach (FrameExpression fe in iter.Modifies.Expressions) {
        ResolveFrameExpressionTopLevel(fe, iter);
      }
      foreach (AttributedExpression e in iter.Requires) {
        VisitAttributes(e, resolutionContext);
        VisitExpression(e.E, resolutionContext);
      }

      currentClass = iter;
      foreach (AttributedExpression e in iter.YieldRequires) {
        VisitAttributes(e, resolutionContext);
        VisitExpression(e.E, resolutionContext);
      }
      foreach (AttributedExpression e in iter.YieldEnsures) {
        VisitAttributes(e, ResolutionContext.FromCodeContext(iter));
        VisitExpression(e.E, ResolutionContext.FromCodeContext(iter));
      }
      foreach (AttributedExpression e in iter.Ensures) {
        VisitAttributes(e, ResolutionContext.FromCodeContext(iter));
        VisitExpression(e.E, ResolutionContext.FromCodeContext(iter));
      }

      // Resolve body
      if (iter.Body != null) {
        ResolveBlockStatement(iter.Body, ResolutionContext.FromCodeContext(iter));
      }

      currentClass = null;
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
      VisitAttributes(f, new ResolutionContext(f, false));

      foreach (var formal in f.Formals) {
        VisitUserProvidedType(formal.Type, ResolutionContext.FromCodeContext(f));
      }
      VisitUserProvidedType(f.ResultType, ResolutionContext.FromCodeContext(f));

      ResolveParameterDefaultValues(f.Formals, ResolutionContext.FromCodeContext(f));

      foreach (AttributedExpression e in f.Req) {
        VisitAttributes(e, new ResolutionContext(f, f is TwoStateFunction));
        VisitExpression(e.E, new ResolutionContext(f, f is TwoStateFunction));
      }
      foreach (FrameExpression fr in f.Reads) {
        ResolveFrameExpressionTopLevel(fr, f);
      }
      foreach (AttributedExpression e in f.Ens) {
        VisitAttributes(e, new ResolutionContext(f, f is TwoStateFunction));
        VisitExpression(e.E, new ResolutionContext(f, f is TwoStateFunction) with { InFunctionPostcondition = true });
      }
      VisitAttributes(f.Decreases, new ResolutionContext(f, f is TwoStateFunction));
      foreach (Expression r in f.Decreases.Expressions) {
        VisitExpression(r, new ResolutionContext(f, f is TwoStateFunction));
      }

      if (f.ByMethodBody != null) {
        // The following conditions are assured by the parser and other callers of the Function constructor
        Contract.Assert(f.Body != null);
        Contract.Assert(!f.IsGhost);
      }
      if (f.Body != null) {
        VisitExpression(f.Body, new ResolutionContext(f, f is TwoStateFunction));
      }
    }

    public void VisitExpression(Expression expr, ResolutionContext resolutionContext) {
      Contract.Requires(expr != null);
      Contract.Requires(resolutionContext != null);

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
        VisitExpression(e.E, resolutionContext);

      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        ResolveDatatypeValue(resolutionContext, dtv, dtv.Type.AsDatatype, null);

      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        foreach (Expression ee in e.Elements) {
          VisitExpression(ee, resolutionContext);
        }

      } else if (expr is MapDisplayExpr) {
        MapDisplayExpr e = (MapDisplayExpr)expr;
        foreach (ExpressionPair p in e.Elements) {
          VisitExpression(p.A, resolutionContext);
          VisitExpression(p.B, resolutionContext);
        }

      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        VisitExpression(e.Obj, resolutionContext);
        if (e.Member is Function fn) {
          AddCallGraphEdge(resolutionContext.CodeContext, fn, e, false);
        } else {
          var field = (Field)e.Member;
          AddCallGraphEdgeForField(resolutionContext.CodeContext, field, e);
        }

      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        VisitExpression(e.Seq, resolutionContext);
        if (e.E0 != null) {
          VisitExpression(e.E0, resolutionContext);
        }
        if (e.E1 != null) {
          VisitExpression(e.E1, resolutionContext);
        }

      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;

        VisitExpression(e.Array, resolutionContext);
        foreach (Expression idx in e.Indices) {
          VisitExpression(idx, resolutionContext);
        }

      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        VisitExpression(e.Seq, resolutionContext);
        VisitExpression(e.Index, resolutionContext);
        VisitExpression(e.Value, resolutionContext);

      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        ResolveFunctionCallExpr(e, resolutionContext);

      } else if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        VisitExpression(e.Function, resolutionContext);
        foreach (var arg in e.Args) {
          VisitExpression(arg, resolutionContext);
        }

      } else if (expr is SeqConstructionExpr) {
        var e = (SeqConstructionExpr)expr;
        VisitUserProvidedType(e.ExplicitElementType ?? new InferredTypeProxy(), resolutionContext);
        VisitExpression(e.N, resolutionContext);
        VisitExpression(e.Initializer, resolutionContext);

      } else if (expr is MultiSetFormingExpr) {
        MultiSetFormingExpr e = (MultiSetFormingExpr)expr;
        VisitExpression(e.E, resolutionContext);

      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        VisitExpression(e.E, new ResolutionContext(resolutionContext.CodeContext, false) with { InOld = true });

      } else if (expr is UnchangedExpr) {
        var e = (UnchangedExpr)expr;
        foreach (var fe in e.Frame) {
          ResolveFrameExpression(fe, resolutionContext);
        }

      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        VisitExpression(e.E, resolutionContext);

      } else if (expr is TypeUnaryExpr) {
        var e = (TypeUnaryExpr)expr;
        VisitExpression(e.E, resolutionContext);
        VisitUserProvidedType(e.ToType, resolutionContext);

      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        VisitExpression(e.E0, resolutionContext);
        VisitExpression(e.E1, resolutionContext);

      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        VisitExpression(e.E0, resolutionContext);
        VisitExpression(e.E1, resolutionContext);
        VisitExpression(e.E2, resolutionContext);

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        if (e.Exact) {
          foreach (var rhs in e.RHSs) {
            VisitExpression(rhs, resolutionContext);
          }
          var i = 0;
          foreach (var lhs in e.LHSs) {
            var rhsType = i < e.RHSs.Count ? e.RHSs[i].Type : new InferredTypeProxy();
            ResolveCasePattern(lhs, resolutionContext);
            // Check for duplicate names now, because not until after resolving the case pattern do we know if identifiers inside it refer to bound variables or nullary constructors
            i++;
          }
        } else {
          // let-such-that expression
          foreach (var lhs in e.LHSs) {
            var v = lhs.Var;
            VisitUserProvidedType(v.Type, resolutionContext);
          }
          foreach (var rhs in e.RHSs) {
            VisitExpression(rhs, resolutionContext);
          }
        }
        VisitExpression(e.Body, resolutionContext);
        VisitAttributes(e, resolutionContext);
      } else if (expr is QuantifierExpr) {
        var e = (QuantifierExpr)expr;
        if (resolutionContext.CodeContext is Function) {
          ((Function)resolutionContext.CodeContext).ContainsQuantifier = true;
        }
        Contract.Assert(e.SplitQuantifier == null); // No split quantifiers during resolution
        foreach (BoundVar v in e.BoundVars) {
          VisitUserProvidedType(v.Type, resolutionContext);
        }
        if (e.Range != null) {
          VisitExpression(e.Range, resolutionContext);
        }
        VisitExpression(e.Term, resolutionContext);
        VisitAttributes(e, resolutionContext);

      } else if (expr is SetComprehension) {
        var e = (SetComprehension)expr;
        foreach (BoundVar v in e.BoundVars) {
          VisitUserProvidedType(v.Type, resolutionContext);
        }
        VisitExpression(e.Range, resolutionContext);
        VisitExpression(e.Term, resolutionContext);
        VisitAttributes(e, resolutionContext);

      } else if (expr is MapComprehension) {
        var e = (MapComprehension)expr;
        foreach (BoundVar v in e.BoundVars) {
          VisitUserProvidedType(v.Type, resolutionContext);
        }
        VisitExpression(e.Range, resolutionContext);
        if (e.TermLeft != null) {
          VisitExpression(e.TermLeft, resolutionContext);
        }
        VisitExpression(e.Term, resolutionContext);

        VisitAttributes(e, resolutionContext);

      } else if (expr is LambdaExpr) {
        var e = (LambdaExpr)expr;
        foreach (BoundVar v in e.BoundVars) {
          VisitUserProvidedType(v.Type, resolutionContext);
        }

        if (e.Range != null) {
          VisitExpression(e.Range, resolutionContext);
        }
        foreach (var read in e.Reads) {
          ResolveFrameExpression(read, resolutionContext);
        }
        VisitExpression(e.Term, resolutionContext);

      } else if (expr is WildcardExpr) {
      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        ResolveStatement(e.S, resolutionContext);
        VisitExpression(e.E, resolutionContext);

      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        VisitExpression(e.Test, resolutionContext);
        VisitExpression(e.Thn, resolutionContext);
        VisitExpression(e.Els, resolutionContext);

      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        VisitExpression(e.Source, resolutionContext);
        foreach (MatchCaseExpr mc in e.Cases) {
          if (mc.Arguments != null) {
            foreach (BoundVar v in mc.Arguments) {
              VisitUserProvidedType(v.Type, resolutionContext);
            }
          }
          VisitExpression(mc.Body, resolutionContext);
        }

      } else {
        Contract.Assert(false);
        throw new cce.UnreachableException(); // unexpected expression
      }
    }

    private void ResolveDatatypeValue(ResolutionContext resolutionContext, DatatypeValue dtv, DatatypeDecl dt, Type ty, bool complain = true) {
      Contract.Requires(resolutionContext != null);
      Contract.Requires(dtv != null);
      Contract.Requires(dt != null);
      Contract.Requires(ty == null || (ty.AsDatatype == dt && ty.TypeArgs.Count == dt.TypeArgs.Count));

      dtv.Bindings.Arguments.ForEach(arg => VisitExpression(arg, resolutionContext));

      if (CodeContextWrapper.Unwrap(resolutionContext.CodeContext) is ICallable caller && caller.EnclosingModule == dt.EnclosingModuleDefinition) {
        caller.EnclosingModule.CallGraph.AddEdge(caller, dt);
      }
    }

    public void ResolveFunctionCallExpr(FunctionCallExpr e, ResolutionContext resolutionContext) {
      VisitExpression(e.Receiver, resolutionContext);

      var function = e.Function;
      if (function is ExtremePredicate extremePredicate) {
        extremePredicate.Uses.Add(e);
      }

      // type check the arguments
      e.Bindings.Arguments.ForEach(arg => VisitExpression(arg, resolutionContext));

      AddCallGraphEdge(resolutionContext.CodeContext, function, e, IsFunctionReturnValue(function, e.Bindings.ArgumentBindings, resolutionContext));
    }

    void ResolveFrameExpressionTopLevel(FrameExpression fe, ICodeContext codeContext) {
      ResolveFrameExpression(fe, new ResolutionContext(codeContext, false));
    }

    void ResolveFrameExpression(FrameExpression fe, ResolutionContext resolutionContext) {
      Contract.Requires(fe != null);
      Contract.Requires(resolutionContext != null);

      VisitExpression(fe.E, resolutionContext);
    }

    void ResolveParameterDefaultValues(List<Formal> formals, ResolutionContext resolutionContext) {
      Contract.Requires(formals != null);
      Contract.Requires(resolutionContext != null);

      foreach (var formal in formals) {
        var d = formal.DefaultValue;
        if (d != null) {
          VisitExpression(d, resolutionContext);
        }
      }
    }

    private bool IsFunctionReturnValue(Function fn, List<ActualBinding> args, ResolutionContext resolutionContext) {
      // if the call is in post-condition and it is calling itself, and the arguments matches
      // formal parameters, then it denotes function return value.
      return args != null && resolutionContext.InFunctionPostcondition && resolutionContext.CodeContext == fn &&
             args.All(binding => binding.Actual.Resolved is IdentifierExpr ide && ide.Var is Formal);
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
        VisitUserProvidedType(p.Type, new ResolutionContext(m, m is TwoStateLemma));
      }
      foreach (var p in m.Outs) {
        VisitUserProvidedType(p.Type, new ResolutionContext(m, true));
      }

      // Add in-parameters to the scope, but don't care about any duplication errors, since they have already been reported
      ResolveParameterDefaultValues(m.Ins, new ResolutionContext(m, m is TwoStateLemma));

      // Start resolving specification...
      foreach (AttributedExpression e in m.Req) {
        VisitAttributes(e, new ResolutionContext(m, m is TwoStateLemma));
        VisitExpression(e.E, new ResolutionContext(m, m is TwoStateLemma));
      }

      VisitAttributes(m.Mod, new ResolutionContext(m, false));
      foreach (FrameExpression fe in m.Mod.Expressions) {
        ResolveFrameExpressionTopLevel(fe, m);
      }
      VisitAttributes(m.Decreases, new ResolutionContext(m, false));
      foreach (Expression e in m.Decreases.Expressions) {
        VisitExpression(e, new ResolutionContext(m, m is TwoStateLemma));
      }

      // ... continue resolving specification
      foreach (AttributedExpression e in m.Ens) {
        VisitAttributes(e, new ResolutionContext(m, true));
        VisitExpression(e.E, new ResolutionContext(m, true));
      }

      // Resolve body
      if (m.Body != null) {
        ResolveBlockStatement(m.Body, ResolutionContext.FromCodeContext(m));
      }

      // attributes are allowed to mention both in- and out-parameters (including the implicit _k, for greatest lemmas)
      VisitAttributes(m, new ResolutionContext(m, m is TwoStateLemma));
    }

    void ResolveBlockStatement(BlockStmt blockStmt, ResolutionContext resolutionContext) {
      Contract.Requires(blockStmt != null);
      Contract.Requires(resolutionContext != null);

      if (blockStmt is DividedBlockStmt) {
        var div = (DividedBlockStmt)blockStmt;
        ResolveStatementList(div.BodyInit, resolutionContext with { InFirstPhaseConstructor = true });
        ResolveStatementList(div.BodyProper, resolutionContext);
      } else {
        ResolveStatementList(blockStmt.Body, resolutionContext);
      }
    }

    void ResolveStatementList(List<Statement> statements, ResolutionContext resolutionContext) {
      foreach (var stmt in statements) {
        ResolveStatementWithLabels(stmt, resolutionContext);
      }
    }

    void ResolveStatementWithLabels(Statement stmt, ResolutionContext resolutionContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(resolutionContext != null);

      ResolveStatement(stmt, resolutionContext);
    }

    public void ResolveStatement(Statement stmt, ResolutionContext resolutionContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(resolutionContext != null);
      if (!(stmt is ForallStmt || stmt is ForLoopStmt)) {  // "forall" and "for" statements do their own attribute resolution below
        VisitAttributes(stmt, resolutionContext);
      }

      if (stmt is PredicateStmt) {
        PredicateStmt s = (PredicateStmt)stmt;
        var assertStmt = stmt as AssertStmt;
        VisitExpression(s.Expr, resolutionContext);
        if (assertStmt != null && assertStmt.Proof != null) {
          // clear the labels for the duration of checking the proof body, because break statements are not allowed to leave a the proof body
          ResolveStatement(assertStmt.Proof, resolutionContext);
        }
        if (stmt is ExpectStmt expectStmt) {
          VisitExpression(expectStmt.Message, resolutionContext);
        }

      } else if (stmt is PrintStmt) {
        var s = (PrintStmt)stmt;
        s.Args.Iter(e => VisitExpression(e, resolutionContext));

      } else if (stmt is RevealStmt) {
        var s = (RevealStmt)stmt;
        ResolveStatementList(s.ResolvedStatements, resolutionContext);

      } else if (stmt is BreakStmt) {

      } else if (stmt is ProduceStmt) {
        var kind = stmt is YieldStmt ? "yield" : "return";
        var s = (ProduceStmt)stmt;
        if (s.HiddenUpdate != null) {
          ResolveStatement(s.HiddenUpdate, resolutionContext);
        }

      } else if (stmt is ConcreteUpdateStatement) {
        ResolveConcreteUpdateStmt((ConcreteUpdateStatement)stmt, resolutionContext);

      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        // We have four cases.
        Contract.Assert(s.Update == null || s.Update is AssignSuchThatStmt || s.Update is UpdateStmt || s.Update is AssignOrReturnStmt);
        foreach (var local in s.Locals) {
          VisitUserProvidedType(local.OptionalType, resolutionContext);
        }

        foreach (var local in s.Locals) {
          VisitAttributes(local, resolutionContext);
        }

        if (s.Update != null) {
          ResolveConcreteUpdateStmt(s.Update, resolutionContext);
        }

      } else if (stmt is VarDeclPattern) {
        VarDeclPattern s = (VarDeclPattern)stmt;
        foreach (var local in s.LocalVars) {
          VisitUserProvidedType(local.OptionalType, resolutionContext);
        }
        VisitExpression(s.RHS, resolutionContext);
        ResolveCasePattern(s.LHS, resolutionContext);
        // Check for duplicate names now, because not until after resolving the case pattern do we know if identifiers inside it refer to bound variables or nullary constructors

      } else if (stmt is AssignStmt) {
        AssignStmt s = (AssignStmt)stmt;
        VisitExpression(s.Lhs, resolutionContext);  // allow ghosts for now, tighted up below
        var lhs = s.Lhs.Resolved;
        Type lhsType = s.Lhs.Type;
        if (s.Rhs is ExprRhs) {
          ExprRhs rr = (ExprRhs)s.Rhs;
          VisitExpression(rr.Expr, resolutionContext);
        } else if (s.Rhs is TypeRhs) {
          TypeRhs rr = (TypeRhs)s.Rhs;
          ResolveTypeRhs(rr, stmt, resolutionContext);
        } else if (s.Rhs is HavocRhs) {
          // nothing else to do
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected RHS
        }

      } else if (stmt is CallStmt) {
        CallStmt s = (CallStmt)stmt;
        AddCallGraphEdge(s, resolutionContext);
        VisitExpression(s.Receiver, resolutionContext);
        s.Bindings.Arguments.ForEach(arg => VisitExpression(arg, resolutionContext));

      } else if (stmt is BlockStmt) {
        var s = (BlockStmt)stmt;
        ResolveBlockStatement(s, resolutionContext);

      } else if (stmt is IfStmt) {
        IfStmt s = (IfStmt)stmt;
        if (s.Guard != null) {
          VisitExpression(s.Guard, resolutionContext);
        }

        ResolveBlockStatement(s.Thn, resolutionContext);

        if (s.Els != null) {
          ResolveStatement(s.Els, resolutionContext);
        }

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        ResolveAlternatives(s.Alternatives, null, resolutionContext);

      } else if (stmt is OneBodyLoopStmt) {
        var s = (OneBodyLoopStmt)stmt;
        if (s is WhileStmt whileS && whileS.Guard != null) {
          VisitExpression(whileS.Guard, resolutionContext);
        } else if (s is ForLoopStmt forS) {
          var loopIndex = forS.LoopIndex;
          VisitUserProvidedType(loopIndex.Type, resolutionContext);

          VisitExpression(forS.Start, resolutionContext);
          if (forS.End != null) {
            VisitExpression(forS.End, resolutionContext);
          }

          VisitAttributes(s, resolutionContext);
        }

        ResolveLoopSpecificationComponents(s.Invariants, s.Decreases, s.Mod, resolutionContext);

        if (s.Body != null) {
          ResolveStatement(s.Body, resolutionContext);
        }

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        ResolveAlternatives(s.Alternatives, s, resolutionContext);
        ResolveLoopSpecificationComponents(s.Invariants, s.Decreases, s.Mod, resolutionContext);

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;

        foreach (BoundVar v in s.BoundVars) {
          VisitUserProvidedType(v.Type, resolutionContext);
        }
        VisitExpression(s.Range, resolutionContext);
        foreach (var ens in s.Ens) {
          VisitExpression(ens.E, resolutionContext);
        }
        VisitAttributes(s, resolutionContext);

        if (s.Body != null) {
          ResolveStatement(s.Body, resolutionContext);
        }

        if (s.ForallExpressions != null) {
          foreach (Expression expr in s.ForallExpressions) {
            VisitExpression(expr, resolutionContext);
          }
        }

      } else if (stmt is ModifyStmt) {
        var s = (ModifyStmt)stmt;
        VisitAttributes(s.Mod, resolutionContext);
        foreach (FrameExpression fe in s.Mod.Expressions) {
          ResolveFrameExpression(fe, resolutionContext);
        }
        if (s.Body != null) {
          ResolveBlockStatement(s.Body, resolutionContext);
        }

      } else if (stmt is CalcStmt) {
        CalcStmt s = (CalcStmt)stmt;

        foreach (var line in s.Lines) {
          VisitExpression(line, resolutionContext);
        }

        foreach (var h in s.Hints) {
          ResolveStatementList(h.Body, resolutionContext);
        }

      } else if (stmt is MatchStmt) {
        ResolveMatchStmt((MatchStmt)stmt, resolutionContext);

      } else if (stmt is SkeletonStatement) {
        var s = (SkeletonStatement)stmt;
        if (s.S != null) {
          ResolveStatement(s.S, resolutionContext);
        }

      } else if (stmt is ConcreteSyntaxStatement) {
        var s = (ConcreteSyntaxStatement)stmt;
        ResolveStatement(s.ResolvedStatement, resolutionContext);

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    private void ResolveConcreteUpdateStmt(ConcreteUpdateStatement s, ResolutionContext resolutionContext) {
      Contract.Requires(resolutionContext != null);

      var lhsNameSet = new HashSet<string>();  // used to check for duplicate identifiers on the left (full duplication checking for references and the like is done during verification)
      foreach (var lhs in s.Lhss) {
        VisitExpression(lhs, resolutionContext);
      }

      // RHSs
      if (s is AssignSuchThatStmt assignSuchThatStmt) {
        VisitExpression(assignSuchThatStmt.Expr, resolutionContext);
      } else if (s is UpdateStmt updateStatement) {
        ResolveStatementList(updateStatement.ResolvedStatements, resolutionContext);
      } else if (s is AssignOrReturnStmt assignOrReturnStmt) {
        ResolveStatementList(assignOrReturnStmt.ResolvedStatements, resolutionContext);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
      VisitAttributes(s, resolutionContext);
    }

    void ResolveTypeRhs(TypeRhs rr, Statement stmt, ResolutionContext resolutionContext) {
      Contract.Requires(rr != null);
      Contract.Requires(stmt != null);
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(Contract.Result<Type>() != null);

      if (rr.ArrayDimensions != null) {
        // ---------- new T[EE]    OR    new T[EE] (elementInit)
        Contract.Assert(rr.Bindings == null && rr.Path == null && rr.InitCall == null);
        VisitUserProvidedType(rr.EType, resolutionContext);
        foreach (Expression dim in rr.ArrayDimensions) {
          Contract.Assert(dim != null);
          VisitExpression(dim, resolutionContext);
        }
        if (rr.ElementInit != null) {
          VisitExpression(rr.ElementInit, resolutionContext);
        } else if (rr.InitDisplay != null) {
          foreach (var v in rr.InitDisplay) {
            VisitExpression(v, resolutionContext);
          }
        }
      } else {
        if (rr.Bindings == null) {
          VisitUserProvidedType(rr.EType, resolutionContext);
        } else {
          // ---------- new C.Init(EE)
          ResolveStatement(rr.InitCall, resolutionContext);
        }
      }
    }

    void ResolveAlternatives(List<GuardedAlternative> alternatives, AlternativeLoopStmt loopToCatchBreaks, ResolutionContext resolutionContext) {
      Contract.Requires(alternatives != null);
      Contract.Requires(resolutionContext != null);

      // first, resolve the guards
      foreach (var alternative in alternatives) {
        VisitExpression(alternative.Guard, resolutionContext);
      }

      foreach (var alternative in alternatives) {
        VisitAttributes(alternative, resolutionContext);
        ResolveStatementList(alternative.Body, resolutionContext);
      }
    }

    private void ResolveLoopSpecificationComponents(List<AttributedExpression> invariants, Specification<Expression> decreases,
      Specification<FrameExpression> modifies, ResolutionContext resolutionContext) {
      Contract.Requires(invariants != null);
      Contract.Requires(decreases != null);
      Contract.Requires(modifies != null);
      Contract.Requires(resolutionContext != null);

      foreach (AttributedExpression inv in invariants) {
        VisitAttributes(inv, resolutionContext);
        VisitExpression(inv.E, resolutionContext);
      }

      VisitAttributes(decreases, resolutionContext);
      foreach (Expression e in decreases.Expressions) {
        VisitExpression(e, resolutionContext);
      }

      VisitAttributes(modifies, resolutionContext);
      if (modifies.Expressions != null) {
        foreach (FrameExpression fe in modifies.Expressions) {
          ResolveFrameExpression(fe, resolutionContext);
        }
      }
    }

    void ResolveMatchStmt(MatchStmt s, ResolutionContext resolutionContext) {
      Contract.Requires(s != null);
      Contract.Requires(resolutionContext != null);
      Contract.Requires(s.OrigUnresolved == null);

      VisitExpression(s.Source, resolutionContext);
      foreach (MatchCaseStmt mc in s.Cases) {
        if (mc.Arguments != null) {
          foreach (BoundVar v in mc.Arguments) {
            VisitUserProvidedType(v.Type, resolutionContext);
          }
        }
        ResolveStatementList(mc.Body, resolutionContext);
      }
    }

    void ResolveCasePattern<VT>(CasePattern<VT> pat, ResolutionContext resolutionContext) where VT : IVariable {
      Contract.Requires(pat != null);
      Contract.Requires(resolutionContext != null);

      if (pat.Var != null) {
        // this is a simple resolution
        var v = pat.Var;
        VisitUserProvidedType(v.Type, resolutionContext);
        return;
      }
      var j = 0;
      if (pat.Arguments != null) {
        foreach (var arg in pat.Arguments) {
          var formal = pat.Ctor.Formals[j];
          ResolveCasePattern(arg, resolutionContext.WithGhost(resolutionContext.IsGhost || formal.IsGhost));
          j++;
        }
      }
    }

    void VisitUserProvidedType(Type type, ResolutionContext resolutionContext) {
      AddTypeDependencyEdges(resolutionContext.CodeContext, type);
    }
  }
}
