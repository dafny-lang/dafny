using System.Collections.Generic;
using System.Diagnostics.Contracts;
using JetBrains.Annotations;
using static Microsoft.Dafny.RewriterErrors;

namespace Microsoft.Dafny;

public class InductionRewriter : IRewriter {
  internal InductionRewriter(ErrorReporter reporter) : base(reporter) {
    Contract.Requires(reporter != null);
  }

  internal override void PostDecreasesResolve(ModuleDefinition m) {
    if (Reporter.Options.Induction == 0) {
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

        if (decl is NewtypeDecl { Constraint: { } constraint }) {
          var visitor = new InductionVisitor(this);
          visitor.Visit(constraint);
        }
      }
    }
  }

  void ProcessMethodExpressions(Method method) {
    Contract.Requires(method != null);
    var visitor = new InductionVisitor(this);
    method.Req.ForEach(mfe => visitor.Visit(mfe.E));
    method.Ens.ForEach(mfe => visitor.Visit(mfe.E));
    if (method.Body != null) {
      visitor.Visit(method.Body);
    }
  }

  void ProcessFunctionExpressions(Function function) {
    Contract.Requires(function != null);
    var visitor = new InductionVisitor(this);
    function.Req.ForEach(visitor.Visit);
    function.Ens.ForEach(visitor.Visit);
    if (function.Body != null) {
      visitor.Visit(function.Body);
    }
  }

  void ComputeLemmaInduction(Method method) {
    Contract.Requires(method != null);
    if (method is Lemma or PrefixLemma && method is { Body: not null, Outs: { Count: 0 } }) {
      Expression pre = Expression.CreateBoolLiteral(method.tok, true);
      foreach (var req in method.Req) {
        pre = Expression.CreateAnd(pre, req.E);
      }
      Expression post = Expression.CreateBoolLiteral(method.tok, true);
      foreach (var ens in method.Ens) {
        post = Expression.CreateAnd(post, ens.E);
      }
      ComputeInductionVariables(method.tok, method.Ins, Expression.CreateImplies(pre, post), method, ref method.Attributes);
    }
  }

  /// <summary>
  /// Look at the command-line options and any {:induction} attribute to determine a good list of induction
  /// variables. If there are any, then record them in an attribute {:_induction ...} added to "attributes".
  /// "body" is the condition that the induction would support.
  /// </summary>
  void ComputeInductionVariables<TVarType>(IToken tok, List<TVarType> boundVars, Expression body,
    [CanBeNull] Method lemma, ref Attributes attributes) where TVarType : class, IVariable {
    Contract.Requires(tok != null);
    Contract.Requires(boundVars != null);
    Contract.Requires(body != null);
    Contract.Requires(Reporter.Options.Induction != 0);

    var args = Attributes.FindExpressions(attributes,
      "induction"); // we only look at the first one we find, since it overrides any other ones
    if (args == null) {
      if (Reporter.Options.Induction < 2) {
        // No explicit induction variables and we're asked not to infer anything, so we're done
        return;
      } else if (Reporter.Options.Induction == 2 && lemma != null) {
        // We're asked to infer induction variables only for quantifiers, not for lemmas
        return;
      } else if (Reporter.Options.Induction == 4 && lemma == null) {
        // We're asked to infer induction variables only for lemmas, not for quantifiers
        return;
      }
      // GO INFER below (only select boundVars)
    } else if (args.Count == 0) {
      // {:induction} is treated the same as {:induction true}, which says to automatically infer induction variables
      // GO INFER below (all boundVars)
    } else if (args.Count == 1 && args[0] is LiteralExpr { Value: bool and var boolValue }) {
      // {:induction false} or {:induction true}
      if (!boolValue) {
        // we're told not to infer anything
        return;
      }
      // GO INFER below (all boundVars)
    } else {
      // Here, we're expecting the arguments to {:induction args} to be a sublist of "this;boundVars", where "this" is allowed only
      // if "lemma" denotes an instance lemma.
      var goodArguments = new List<Expression>();
      var i = lemma is { IsStatic: false }
        ? -1
        : 0; // -1 says it's okay to see "this" or any other parameter; 0 <= i says it's okay to see parameter i or higher
      foreach (var arg in args) {
        if (arg.Resolved is IdentifierExpr ie) {
          var j = boundVars.FindIndex(v => v == ie.Var);
          if (0 <= j && i <= j) {
            goodArguments.Add(ie);
            i = j + 1;
            continue;
          }

          if (0 <= j) {
            ReportWarning(ErrorId.rw_induction_arguments_quantifier_mismatch, arg.tok,
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

          ReportWarning(ErrorId.rw_induction_arguments_lemma_mismatch, arg.tok,
            "lemma parameters given as :induction arguments must be given in the same order as in the lemma; ignoring attribute");
          return;
        }

        ReportWarning(ErrorId.rw_invalid_induction_attribute, arg.tok,
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
    if (lemma is { IsStatic: false }) {
      if (args != null || FreeVariablesUtil.ContainsFreeVariable(body, true, null)) {
        inductionVariables.Add(new ThisExpr(lemma));
      }
    }

    foreach (IVariable n in boundVars) {
      if (!(n.Type.IsTypeParameter || n.Type.IsAbstractType || n.Type.IsInternalTypeSynonym) &&
          (args != null || InductionHeuristic.VarOccursInArgumentToRecursiveFunction(Reporter.Options, body, n))) {
        inductionVariables.Add(new IdentifierExpr(n.Tok, n));
      }
    }

    if (inductionVariables.Count != 0) {
      // We found something usable, so let's record that in an attribute
      attributes = new Attributes("_induction", inductionVariables, attributes);
      // And since we're inferring something, let's also report that in a hover text.
      var s = Printer.OneAttributeToString(Reporter.Options, attributes, "induction");
      if (lemma is PrefixLemma) {
        s = lemma.Name + " " + s;
      }

      Reporter.Info(MessageSource.Rewriter, tok, s);
    }
  }

  class InductionVisitor : BottomUpVisitor {
    readonly InductionRewriter IndRewriter;

    public InductionVisitor(InductionRewriter inductionRewriter) {
      Contract.Requires(inductionRewriter != null);
      IndRewriter = inductionRewriter;
    }

    protected override void VisitOneExpr(Expression expr) {
      if (expr is QuantifierExpr { SplitQuantifier: null } q) {
        IndRewriter.ComputeInductionVariables(q.tok, q.BoundVars, q.LogicalBody(), null, ref q.Attributes);
      }
    }
  }
}