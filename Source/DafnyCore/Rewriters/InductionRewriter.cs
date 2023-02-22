using System.Collections.Generic;
using System.Diagnostics.Contracts;
using static Microsoft.Dafny.ErrorRegistry;

namespace Microsoft.Dafny;

public class InductionRewriter : IRewriter {
  internal InductionRewriter(ErrorReporter reporter) : base(reporter) {
    Contract.Requires(reporter != null);
  }

  internal override void PostDecreasesResolve(ModuleDefinition m) {
    if (DafnyOptions.O.Induction == 0) {
      // Don't bother inferring :induction attributes.  This will also have the effect of not warning about malformed :induction attributes
    } else {
      foreach (var decl in m.TopLevelDecls) {
        if (decl is TopLevelDeclWithMembers) {
          var cl = (TopLevelDeclWithMembers)decl;
          foreach (var member in cl.Members) {
            if (member is ExtremeLemma) {
              var method = (ExtremeLemma)member;
              ProcessMethodExpressions(method);
              ComputeLemmaInduction(method.PrefixLemma);
              ProcessMethodExpressions(method.PrefixLemma);
            } else if (member is Method) {
              var method = (Method)member;
              ComputeLemmaInduction(method);
              ProcessMethodExpressions(method);
            } else if (member is ExtremePredicate) {
              var function = (ExtremePredicate)member;
              ProcessFunctionExpressions(function);
              ProcessFunctionExpressions(function.PrefixPredicate);
            } else if (member is Function) {
              var function = (Function)member;
              ProcessFunctionExpressions(function);
              if (function.ByMethodDecl != null) {
                ProcessMethodExpressions(function.ByMethodDecl);
              }
            }
          }
        }

        if (decl is NewtypeDecl) {
          var nt = (NewtypeDecl)decl;
          if (nt.Constraint != null) {
            var visitor = new Induction_Visitor(this);
            visitor.Visit(nt.Constraint);
          }
        }
      }
    }
  }

  void ProcessMethodExpressions(Method method) {
    Contract.Requires(method != null);
    var visitor = new Induction_Visitor(this);
    method.Req.ForEach(mfe => visitor.Visit(mfe.E));
    method.Ens.ForEach(mfe => visitor.Visit(mfe.E));
    if (method.Body != null) {
      visitor.Visit(method.Body);
    }
  }

  void ProcessFunctionExpressions(Function function) {
    Contract.Requires(function != null);
    var visitor = new Induction_Visitor(this);
    function.Req.ForEach(visitor.Visit);
    function.Ens.ForEach(visitor.Visit);
    if (function.Body != null) {
      visitor.Visit(function.Body);
    }
  }

  void ComputeLemmaInduction(Method method) {
    Contract.Requires(method != null);
    if (method.Body != null && method.IsGhost && method.Mod.Expressions.Count == 0 && method.Outs.Count == 0 &&
        !(method is ExtremeLemma)) {
      var specs = new List<Expression>();
      method.Req.ForEach(mfe => specs.Add(mfe.E));
      method.Ens.ForEach(mfe => specs.Add(mfe.E));
      ComputeInductionVariables(method.tok, method.Ins, specs, method, ref method.Attributes);
    }
  }

  void ComputeInductionVariables<VarType>(IToken tok, List<VarType> boundVars, List<Expression> searchExprs,
    Method lemma, ref Attributes attributes) where VarType : class, IVariable {
    Contract.Requires(tok != null);
    Contract.Requires(boundVars != null);
    Contract.Requires(searchExprs != null);
    Contract.Requires(DafnyOptions.O.Induction != 0);

    var args = Attributes.FindExpressions(attributes,
      "induction"); // we only look at the first one we find, since it overrides any other ones
    if (args == null) {
      if (DafnyOptions.O.Induction < 2) {
        // No explicit induction variables and we're asked not to infer anything, so we're done
        return;
      } else if (DafnyOptions.O.Induction == 2 && lemma != null) {
        // We're asked to infer induction variables only for quantifiers, not for lemmas
        return;
      } else if (DafnyOptions.O.Induction == 4 && lemma == null) {
        // We're asked to infer induction variables only for lemmas, not for quantifiers
        return;
      }
      // GO INFER below (only select boundVars)
    } else if (args.Count == 0) {
      // {:induction} is treated the same as {:induction true}, which says to automatically infer induction variables
      // GO INFER below (all boundVars)
    } else if (args.Count == 1 && args[0] is LiteralExpr && ((LiteralExpr)args[0]).Value is bool) {
      // {:induction false} or {:induction true}
      if (!(bool)((LiteralExpr)args[0]).Value) {
        // we're told not to infer anything
        return;
      }
      // GO INFER below (all boundVars)
    } else {
      // Here, we're expecting the arguments to {:induction args} to be a sublist of "this;boundVars", where "this" is allowed only
      // if "lemma" denotes an instance lemma.
      var goodArguments = new List<Expression>();
      var i = lemma != null && !lemma.IsStatic
        ? -1
        : 0; // -1 says it's okay to see "this" or any other parameter; 0 <= i says it's okay to see parameter i or higher
      foreach (var arg in args) {
        var ie = arg.Resolved as IdentifierExpr;
        if (ie != null) {
          var j = boundVars.FindIndex(v => v == ie.Var);
          if (0 <= j && i <= j) {
            goodArguments.Add(ie);
            i = j + 1;
            continue;
          }

          if (0 <= j) {
            Reporter.Warning(MessageSource.Rewriter, null, arg.tok,
              "{0}s given as :induction arguments must be given in the same order as in the {1}; ignoring attribute",
              lemma != null ? "lemma parameter" : "bound variable", lemma != null ? "lemma" : "quantifier");
            return;
          }
          // fall through for j < 0
        } else if (lemma != null && arg.Resolved is ThisExpr) {
          if (i < 0) {
            goodArguments.Add(arg.Resolved);
            i = 0;
            continue;
          }

          Reporter.Warning(MessageSource.Rewriter, null, arg.tok,
            "lemma parameters given as :induction arguments must be given in the same order as in the lemma; ignoring attribute");
          return;
        }

        Reporter.Warning(MessageSource.Rewriter, null, arg.tok,
          "invalid :induction attribute argument; expected {0}{1}; ignoring attribute",
          i == 0 ? "'false' or 'true' or " : "",
          lemma != null ? "lemma parameter" : "bound variable");
        return;
      }

      // The argument list was legal, so let's use it for the _induction attribute
      attributes = new Attributes("_induction", goodArguments, attributes);
      return;
    }

    // Okay, here we go, coming up with good induction setting for the given situation
    var inductionVariables = new List<Expression>();
    if (lemma != null && !lemma.IsStatic) {
      if (args != null || searchExprs.Exists(expr => FreeVariablesUtil.ContainsFreeVariable(expr, true, null))) {
        inductionVariables.Add(new ThisExpr(lemma));
      }
    }

    foreach (IVariable n in boundVars) {
      if (!(n.Type.IsTypeParameter || n.Type.IsOpaqueType || n.Type.IsInternalTypeSynonym) && (args != null ||
            searchExprs.Exists(expr => InductionHeuristic.VarOccursInArgumentToRecursiveFunction(expr, n)))) {
        inductionVariables.Add(new IdentifierExpr(n.Tok, n));
      }
    }

    if (inductionVariables.Count != 0) {
      // We found something usable, so let's record that in an attribute
      attributes = new Attributes("_induction", inductionVariables, attributes);
      // And since we're inferring something, let's also report that in a hover text.
      var s = Printer.OneAttributeToString(attributes, "induction");
      if (lemma is PrefixLemma) {
        s = lemma.Name + " " + s;
      }

      Reporter.Info(MessageSource.Rewriter, tok, s);
    }
  }

  class Induction_Visitor : BottomUpVisitor {
    readonly InductionRewriter IndRewriter;

    public Induction_Visitor(InductionRewriter inductionRewriter) {
      Contract.Requires(inductionRewriter != null);
      IndRewriter = inductionRewriter;
    }

    protected override void VisitOneExpr(Expression expr) {
      var q = expr as QuantifierExpr;
      if (q != null && q.SplitQuantifier == null) {
        IndRewriter.ComputeInductionVariables(q.tok, q.BoundVars, new List<Expression>() { q.LogicalBody() }, null,
          ref q.Attributes);
      }
    }
  }
}