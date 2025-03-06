using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
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
    if (method is { IsGhost: true, AllowsAllocation: false, Outs: { Count: 0 }, Body: not null } and not ExtremeLemma) {
      Expression pre = Expression.CreateBoolLiteral(method.Origin, true);
      foreach (var req in method.Req) {
        pre = Expression.CreateAnd(pre, req.E);
      }

      Expression post = Expression.CreateBoolLiteral(method.Origin, true);
      foreach (var ens in method.Ens) {
        post = Expression.CreateAnd(post, ens.E);
      }

      ComputeInductionVariables(method.Origin, method.Ins, Expression.CreateImplies(pre, post), method, ref method.Attributes);
    }
  }

  /// <summary>
  /// Look at the command-line options and any {:induction} attribute to determine a good list of induction
  /// variables. If there are any, then record them in an attribute {:_induction ...} added to "attributes".
  /// "body" is the condition that the induction would support.
  /// </summary>
  void ComputeInductionVariables<TVarType>(IOrigin tok, List<TVarType> boundVars, Expression body,
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
            ReportWarning(ErrorId.rw_induction_arguments_quantifier_mismatch, arg.Origin,
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

          ReportWarning(ErrorId.rw_induction_arguments_lemma_mismatch, arg.Origin,
            "lemma parameters given as :induction arguments must be given in the same order as in the lemma; ignoring attribute");
          return;
        }

        ReportWarning(ErrorId.rw_invalid_induction_attribute, arg.Origin,
          "invalid :induction attribute argument; expected {0}{1}; ignoring attribute",
          i == 0 ? "'false' or 'true' or " : "",
          lemma != null ? "lemma parameter" : "bound variable");
        return;
      }

      // The argument list was legal, so let's use it for the _induction attribute.
      // Next, look for matching patterns for the induction hypothesis.
      if (lemma != null) {
        var triggers = ComputeInductionTriggers(goodArguments, body, lemma.EnclosingClass.EnclosingModuleDefinition, tok, ref attributes);
        ReportInductionTriggers(lemma.Origin, lemma, attributes);
      }

      attributes = new Attributes("_induction", goodArguments, attributes);

      return;
    }

    // Okay, here we go, coming up with good induction setting for the given situation
    var inductionVariables = new List<Expression>();
    if (lemma is { IsStatic: false }) {
      if (args != null || InductionHeuristic.VarOccursInArgumentToRecursiveFunction(Reporter.Options, body, null)) {
        inductionVariables.Add(new ThisExpr(lemma));
      }
    }

    foreach (IVariable n in boundVars) {
      if (!(n.Type.IsTypeParameter || n.Type.IsAbstractType || n.Type.IsInternalTypeSynonym || n.Type.IsArrowType) &&
          (args != null || InductionHeuristic.VarOccursInArgumentToRecursiveFunction(Reporter.Options, body, n))) {
        inductionVariables.Add(new IdentifierExpr(n.Origin, n));
      }
    }

    if (inductionVariables.Count != 0) {
      if (lemma != null) {
        // Compute the induction triggers, but don't report their patterns into attributes yet. Instead,
        // call ReportInductionTriggers only after the "_induction" attribute has been added. This will cause the
        // tooltips to appear in a logical order (showing the induction variables first, followed by the matching patterns).
        var triggers = ComputeInductionTriggers(inductionVariables, body, lemma.EnclosingClass.EnclosingModuleDefinition,
          args != null ? tok : null, ref attributes);
        if (triggers == null && args == null) {
          // The user didn't ask for induction. But since there were candidate induction variables, report an informational message.
          var candidates = $"candidate{Util.Plural(inductionVariables.Count)} {Printer.ExprListToString(Reporter.Options, inductionVariables)}";
          Reporter.Info(MessageSource.Rewriter, tok, $"omitting automatic induction (for induction-variable {candidates}) because of lack of triggers");
          return;
        }
      }

      // We found something usable, so let's record that in an attribute
      attributes = new Attributes("_induction", inductionVariables, attributes);
      // And since we're inferring something, let's also report that in a hover text.
      var s = Printer.OneAttributeToString(Reporter.Options, attributes, "induction");
      if (lemma is PrefixLemma) {
        s = lemma.Name + " " + s;
      }
      Reporter.Info(MessageSource.Rewriter, tok, s);

      ReportInductionTriggers(tok, lemma, attributes);
    }
  }

  /// <summary>
  /// Report as tooltips the matching patterns selected for the induction hypothesis.
  /// </summary>
  private void ReportInductionTriggers(IOrigin tok, [CanBeNull] Method lemma, Attributes attributes) {
    foreach (var trigger in attributes.AsEnumerable().Where(attr => attr.Name == "_inductionTrigger")) {
      var ss = Printer.OneAttributeToString(Reporter.Options, trigger, "inductionTrigger");
      if (lemma is PrefixLemma) {
        ss = lemma.Name + " " + ss;
      }
      Reporter.Info(MessageSource.Rewriter, tok, ss);
    }
  }

  /// <summary>
  /// Obtain and return matching patterns for
  ///     (forall inductionVariables :: body)
  /// If there aren't any, then return null.
  /// This trigger may come from analyzing "body" or from any user-supplied {:inductionTrigger ...} attributes.
  /// Passing {:inductionTrigger} with no arguments causes an empty list to be returned (and disables trigger generation).
  ///
  /// If "errorToken" is non-null and there are no matching patterns, then a warning/info message is emitted.
  /// The selection between warning vs info is done by looking for a {:nowarn} attribute among "attributes".
  /// </summary>
  List<List<Expression>> ComputeInductionTriggers(List<Expression> inductionVariables, Expression body, ModuleDefinition moduleDefinition,
    [CanBeNull] IOrigin errorToken, ref Attributes attributes) {
    Contract.Requires(inductionVariables.Count != 0);

    if (Attributes.Contains(attributes, "inductionTrigger")) {
      // Empty triggers are not valid at the Boogie level, but they indicate that we don't want automatic selection
      Triggers.SplitPartTriggerWriter.DisableEmptyTriggers(attributes, "inductionTrigger");
      return Attributes.FindAllExpressions(attributes, "inductionTrigger") ?? []; // Never null
    }

    // Construct a quantifier, because that's what the trigger-generating machinery expects.
    // We start by creating a new BoundVar for each ThisExpr-or-IdentifierExpr in "inductionVariables".
    var boundVars = new List<BoundVar>();
    var substMap = new Dictionary<IVariable, Expression>();
    var reverseSubstMap = new Dictionary<IVariable, Expression>();
    Expression receiverReplacement = null;
    foreach (var inductionVariableExpr in inductionVariables) {
      var tok = inductionVariableExpr.Origin;
      BoundVar boundVar;
      if (inductionVariableExpr is IdentifierExpr identifierExpr) {
        boundVar = new BoundVar(tok, identifierExpr.Var.Name, identifierExpr.Var.Type);
        substMap.Add(identifierExpr.Var, new IdentifierExpr(tok, boundVar));
      } else {
        Contract.Assert(inductionVariableExpr is ThisExpr);
        boundVar = new BoundVar(tok, "this", inductionVariableExpr.Type);
        receiverReplacement = new IdentifierExpr(tok, boundVar);
      }
      boundVars.Add(boundVar);
      reverseSubstMap.Add(boundVar, inductionVariableExpr);
    }

    var substituter = new Substituter(receiverReplacement, substMap, new Dictionary<TypeParameter, Type>());
    var quantifier = new ForallExpr(body.Origin, boundVars, null, substituter.Substitute(body), null) {
      Type = Type.Bool
    };

    var finder = new Triggers.QuantifierCollector(Reporter);
    var triggersCollector = new Triggers.TriggersCollector(finder.exprsInOldContext, Reporter.Options, moduleDefinition);
    var quantifierCollection = new Triggers.ComprehensionTriggerGenerator(quantifier, Enumerable.Repeat(quantifier, 1), Reporter);
    quantifierCollection.ComputeTriggers(triggersCollector);
    // Get the computed triggers, but only ask for those that do not require additional bound variables. (An alternative to this
    // design would be to add {:matchinglooprewrite false} to "quantifier" above. However, that would cause certain matching loops
    // to be ignored, so it is safer to not include triggers that require additional bound variables.)
    var triggers = quantifierCollection.GetTriggers(false);
    var reverseSubstituter = new Substituter(null, reverseSubstMap, new Dictionary<TypeParameter, Type>());
    var result = triggers.ConvertAll(trigger => trigger.ConvertAll(reverseSubstituter.Substitute));

    if (result.Count == 0 && errorToken != null) {
      // The user explicitly asked for induction (with {:induction}, {:induction true}, or {:induction <variables>}).
      // Respect this choice, but generate a warning that no triggers were found.
      var suppressWarnings = Attributes.Contains(attributes, "nowarn");
      var warningLevel = suppressWarnings ? ErrorLevel.Info : ErrorLevel.Warning;

      Reporter.Message(MessageSource.Rewriter, warningLevel, null, errorToken,
        "Could not find a trigger for the induction hypothesis. Without a trigger, this may cause brittle verification. " +
        "Change or remove the {:induction} attribute to generate a different induction hypothesis, or add {:nowarn} to silence this warning. " +
        "For more information, see the section on quantifier instantiation rules in the reference manual.");
    }

    foreach (var trigger in result) {
      attributes = new Attributes("_inductionTrigger", trigger, attributes);
    }
    return result.Count == 0 ? null : result; // Return null to indicate no results
  }

  class InductionVisitor : BottomUpVisitor {
    readonly InductionRewriter IndRewriter;

    public InductionVisitor(InductionRewriter inductionRewriter) {
      Contract.Requires(inductionRewriter != null);
      IndRewriter = inductionRewriter;
    }

    protected override void VisitOneExpr(Expression expr) {
      if (expr is QuantifierExpr { SplitQuantifier: null } q) {
        IndRewriter.ComputeInductionVariables(q.Origin, q.BoundVars, q.LogicalBody(), null, ref q.Attributes);
      }
    }
  }
}
