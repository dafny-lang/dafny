using System.Collections.Generic;
using System.Linq;
using DafnyCore.Verifier;
using Microsoft.Boogie;
using Microsoft.Dafny.Triggers;
using VC;

namespace Microsoft.Dafny;

public record VerificationTaskResult(IVerificationTask Task, VerificationRunResult Result);

public class ProofDependencyWarnings {


  public static void ReportSuspiciousDependencies(DafnyOptions options, IEnumerable<VerificationTaskResult> parts,
    ErrorReporter reporter, ProofDependencyManager manager) {
    foreach (var resultsForScope in parts.GroupBy(p => p.Task.ScopeId)) {
      WarnAboutSuspiciousDependenciesForImplementation(options,
        reporter,
        manager,
        resultsForScope.Key,
        resultsForScope.Select(p => p.Result).ToList());
    }
  }

  public static void WarnAboutSuspiciousDependenciesUsingStoredPartialResults(DafnyOptions dafnyOptions, ErrorReporter reporter, ProofDependencyManager depManager) {
    var verificationResults = (dafnyOptions.Printer as DafnyConsolePrinter).VerificationResults.ToList();
    var orderedResults =
      verificationResults.OrderBy(vr =>
        (vr.Implementation.Tok.filename, vr.Implementation.Tok.line, vr.Implementation.Tok.col));

    foreach (var (implementation, result) in orderedResults) {
      if (result.Outcome != VcOutcome.Correct) {
        continue;
      }
      var assertCoverage = result.VCResults.Select(e => (e.CoveredElements, new HashSet<DafnyConsolePrinter.AssertCmdPartialCopy>(e.Asserts))).ToList();
      var unusedFunctions = UnusedFunctions(dafnyOptions, depManager, implementation.Name, result.VCResults.SelectMany(r => r.CoveredElements), result.VCResults.SelectMany(r => r.AvailableAxioms));
      WarnAboutSuspiciousDependencies(dafnyOptions, reporter, depManager, implementation.Name, assertCoverage, unusedFunctions);
    }
  }

  public static void WarnAboutSuspiciousDependenciesForImplementation(DafnyOptions dafnyOptions, ErrorReporter reporter,
    ProofDependencyManager depManager, string name,
    IReadOnlyList<VerificationRunResult> results) {
    if (results.Any(r => r.Outcome != SolverOutcome.Valid)) {
      return;
    }
    var distilled = results.Select(r => (r.CoveredElements, DafnyConsolePrinter.DistillVCResult(r)));
    var asserts = distilled.Select(tp => (tp.CoveredElements, new HashSet<DafnyConsolePrinter.AssertCmdPartialCopy>(tp.Item2.Asserts)));
    var unusedFunctions = UnusedFunctions(dafnyOptions, depManager, name, distilled.SelectMany(r => r.CoveredElements), distilled.SelectMany(r => r.Item2.AvailableAxioms));
    WarnAboutSuspiciousDependencies(dafnyOptions, reporter, depManager, name, asserts, unusedFunctions);
  }

  private static List<Function> UnusedFunctions(DafnyOptions dafnyOptions, ProofDependencyManager depManager, string name, IEnumerable<TrackedNodeComponent> coveredElements, IEnumerable<Axiom> axioms) {
    if (!(dafnyOptions.Get(CommonOptionBag.SuggestProofRefactoring) && depManager.idsByMemberName[name].Decl is Method)) {
      return new List<Function>();
    }

    var unusedFunctions = new List<Function>();
    if (depManager.idsByMemberName[name].Decl is not Method m) {
      return unusedFunctions;
    }

    var referencedFunctions = ReferencedFunctions(m);

    var hiddenFunctions = HiddenFunctions(referencedFunctions);

    var usedFunctions = coveredElements.Select(depManager.GetFullIdDependency).OfType<FunctionDefinitionDependency>()
      .Select(dep => dep.function).Deduplicate((a, b) => a.Equals(b));

    unusedFunctions = referencedFunctions.Except(hiddenFunctions).Except(usedFunctions).ToList();

    HashSet<Function> ReferencedFunctions(Method method) {
      var functionCallsInMethod = method.Body != null ? method.Body.AllSubExpressions(false, false).OfType<FunctionCallExpr>() : new List<FunctionCallExpr>();
      var functionDependants = new Dictionary<Function, IEnumerable<Function>>();

      foreach (var fce in functionCallsInMethod) {
        var fun = fce.Function;
        if (!functionDependants.ContainsKey(fun)) {
          functionDependants[fun] = Dependents(fun);
        }

        continue;

        IEnumerable<Function> Dependents(Function fn) {
          var queue = new Queue<Function>(new[] { fn });
          var visited = new HashSet<Function>();
          while (queue.Any()) {
            var f = queue.Dequeue();
            visited.Add(f);

            f.SubExpressions.SelectMany(AllSubFunctions).Where(fn => !visited.Contains(fn)).ForEach(queue.Enqueue);
            continue;

            IEnumerable<Function> AllSubFunctions(Expression e) {
              return e.SubExpressions.OfType<FunctionCallExpr>().Select(fce => fce.Function)
                .Concat(e.SubExpressions.SelectMany(AllSubFunctions));
            }
          }
          return visited.ToList();
        }
      }

      var hashSet = new HashSet<Function>();
      foreach (var (f, deps) in functionDependants) {
        hashSet.Add(f);
        hashSet.UnionWith(deps);
      }

      return hashSet;
    }

    HashSet<Function> HiddenFunctions(HashSet<Function> functions) {
      var hiddenFunctions = new HashSet<Function>(functions);

      foreach (var visibleFunction in axioms.Select(GetFunctionFromAttributed).Where(f => f != null)) {
        hiddenFunctions.Remove(visibleFunction);
      }

      return hiddenFunctions;

      Function GetFunctionFromAttributed(ICarriesAttributes construct) {
        var values = construct.FindAllAttributes("id");
        if (!values.Any()) {
          return null;
        }
        var id = (string)values.Last().Params.First();
        if (depManager.ProofDependenciesById.TryGetValue(id, out var dep) && dep is FunctionDefinitionDependency fdd) {
          return fdd.function;
        }
        return null;
      }
    }
    return unusedFunctions;
  }

  private static void WarnAboutSuspiciousDependencies(DafnyOptions dafnyOptions, ErrorReporter reporter, ProofDependencyManager depManager,
    string scopeName, IEnumerable<(IEnumerable<TrackedNodeComponent> CoveredElements, HashSet<DafnyConsolePrinter.AssertCmdPartialCopy>)> assertCoverage, List<Function> unusedFunctions) {
    var potentialDependencies = depManager.GetPotentialDependenciesForDefinition(scopeName);
    var coveredElements = assertCoverage.SelectMany(tp => tp.CoveredElements);
    var usedDependencies =
      coveredElements
        .Select(depManager.GetFullIdDependency)
        .OrderBy(dep => dep.Range)
        .ThenBy(dep => dep.Description);
    var unusedDependencies =
      potentialDependencies
        .Except(usedDependencies)
        .OrderBy(dep => dep.Range)
        .ThenBy(dep => dep.Description).ToList();

    foreach (var unusedDependency in unusedDependencies) {
      if (dafnyOptions.Get(CommonOptionBag.WarnContradictoryAssumptions)) {
        if (unusedDependency is ProofObligationDependency obligation) {
          if (ShouldWarnVacuous(dafnyOptions, scopeName, obligation)) {
            var message = $"proved using contradictory assumptions: {obligation.Description}";
            if (obligation.ProofObligation is AssertStatementDescription) {
              message += ". (Use the `{:contradiction}` attribute on the `assert` statement to silence.)";
            }
            reporter.Warning(MessageSource.Verifier, "", obligation.Range, message);
          }
        }

        if (unusedDependency is EnsuresDependency ensures) {
          if (ShouldWarnVacuous(dafnyOptions, scopeName, ensures)) {
            reporter.Warning(MessageSource.Verifier, "", ensures.Range,
              $"ensures clause proved using contradictory assumptions");
          }
        }
      }

      if (dafnyOptions.Get(CommonOptionBag.WarnRedundantAssumptions)) {
        if (unusedDependency is RequiresDependency requires) {
          reporter.Warning(MessageSource.Verifier, "", requires.Range, $"unnecessary requires clause");
        }

        if (unusedDependency is AssumptionDependency assumption) {
          if (ShouldWarnUnused(assumption)) {
            reporter.Warning(MessageSource.Verifier, "", assumption.Range,
              $"unnecessary (or partly unnecessary) {assumption.Description}");
          }
        }
      }
    }

    if (dafnyOptions.Get(CommonOptionBag.SuggestProofRefactoring) && depManager.idsByMemberName[scopeName].Decl is Method m) {
      SuggestFunctionHiding(reporter, unusedFunctions, m);
      SuggestByProofRefactoring(reporter, depManager, scopeName, assertCoverage.ToList());
    }
  }

  private static void SuggestFunctionHiding(ErrorReporter reporter, List<Function> unusedFunctions, Method m) {
    if (unusedFunctions.Any()) {
      reporter.Info(MessageSource.Verifier, m.Body.StartToken,
        $"Consider hiding {(unusedFunctions.Count > 1 ? "these functions, which are" : "this function, which is")} unused by the proof: {unusedFunctions.Comma()}");
    }
  }

  private static void SuggestByProofRefactoring(ErrorReporter reporter, ProofDependencyManager depManager,
    string scopeName, List<(IEnumerable<TrackedNodeComponent> CoveredElements, HashSet<DafnyConsolePrinter.AssertCmdPartialCopy> Asserts)> assertCoverage) {
    var dependencyTracker = depManager.GetPotentialDependenciesForDefinition(scopeName).Where(dep => dep is not EnsuresDependency).ToDictionary(dep => dep, _ => new HashSet<DafnyConsolePrinter.AssertCmdPartialCopy> { });

    foreach (var (usedFacts, asserts) in assertCoverage) {
      foreach (var fact in usedFacts) {
        var dep = depManager.GetFullIdDependency(fact);
        _ = dep is not EnsuresDependency &&
            dependencyTracker.TryAdd(dep, new HashSet<DafnyConsolePrinter.AssertCmdPartialCopy>());
        if (dependencyTracker.ContainsKey(dep)) {
          dependencyTracker[dep].UnionWith(asserts);
        }
      }
    }

    foreach (var (dep, lAsserts) in dependencyTracker) {
      foreach (var cmd in lAsserts) {
        if (depManager.ProofDependenciesById.TryGetValue(cmd.Id, out var cmdDep)) {
          if (dep == cmdDep || dep is CallRequiresDependency req && req.call == cmdDep) {
            lAsserts.Remove(cmd);
          }
        }
      }
    }

    foreach (var (dep, lAsserts) in dependencyTracker) {
      if (lAsserts.Count != 1) {
        continue;
      }
      var en = lAsserts.GetEnumerator();
      if (!en.MoveNext()) {
        continue;
      }

      var cmd = en.Current;
      depManager.ProofDependenciesById.TryGetValue(cmd.Id, out var consumer);

      if (consumer != null && (dep == consumer || consumer.Range.Intersects(dep.Range))) {
        continue;
      }

      RangeToken range = null;
      var factProvider = "";
      var factConsumer = "";
      var recomendation = "";
      var completeInformation = true;

      switch (dep) {
        case AssumedProofObligationDependency:
        case AssumptionDependency: {
            range = dep.Range;
            factProvider = "fact";
            recomendation = "moving it into";
            break;
          }
        case RequiresDependency: {
            range = dep.Range;
            factProvider = "requires clause";
            recomendation = "labelling it and revealing it in";
            break;
          }
        default: completeInformation = false; break;
      }

      switch (consumer) {
        case CallDependency call: {
            factConsumer = $"precondtion{(call.call.Method.Req.Count > 1 ? "s" : "")} of the method call {call.RangeString()}";
            break;
          }
        case ProofObligationDependency { ProofObligation: AssertStatementDescription }: {
            factConsumer = $"assertion {consumer.RangeString()}";
            break;
          }
        default: completeInformation = false; break;
      }

      if (completeInformation) {
        reporter.Info(MessageSource.Verifier, range,
          $"This {factProvider} was only used to prove the {factConsumer}. Consider {recomendation} a by-proof.");
      }
    }
  }

  /// <summary>
  /// Some proof obligations that don't show up in the dependency list
  /// are innocuous. Either they come about because of internal Dafny
  /// design choices that the programmer has no control over, or they
  /// just aren't meaningful in context. This method identifies cases
  /// where it doesn't make sense to issue a warning. Many of these
  /// cases should perhaps be eliminated by changing the translator
  /// to not generate vacuous proof goals, but that may be a difficult
  /// change to make.
  /// </summary>
  /// <param name="dep">the dependency to examine</param>
  /// <returns>false to skip warning about the absence of this
  /// dependency, true otherwise</returns>
  private static bool ShouldWarnVacuous(DafnyOptions options, string verboseName, ProofDependency dep) {
    if (dep is ProofObligationDependency poDep) {
      // Dafny generates some assertions about definite assignment whose
      // proofs are always vacuous. Since these aren't written by Dafny
      // programmers, it's safe to just skip them all.
      if (poDep.ProofObligation is DefiniteAssignment) {
        return false;
      }

      // Some proof obligations occur in a context that the Dafny programmer
      // doesn't have control of, so warning about vacuity isn't helpful.
      if (poDep.ProofObligation.ProvedOutsideUserCode) {
        return false;
      }

      // Don't warn about `assert false` being proved vacuously. If it's proved,
      // it must be vacuous, but it's also probably an attempt to prove that a
      // given branch is unreachable (often, but not always, in ghost code).
      var assertedExpr = poDep.ProofObligation.GetAssertedExpr(options);
      if (assertedExpr is not null &&
          Expression.IsBoolLiteral(assertedExpr, out var lit) &&
          lit == false) {
        return false;
      }

      if (poDep.ProofObligation is AssertStatementDescription { IsIntentionalContradiction: true }) {
        return false;
      }
    }

    // Ensures clauses are often proven vacuously during well-formedness checks.
    // There's unfortunately no way to identify these checks once Dafny has
    // been translated to Boogie other than looking at the name. This is a significant
    // limitation, because it means that function ensures clauses that are satisfied
    // only vacuously won't be reported. It would great if we could change the Boogie
    // encoding so that these unreachable-by-construction checks don't exist.
    if (verboseName.Contains("well-formedness") && dep is EnsuresDependency) {
      return false;
    }

    return true;
  }

  /// <summary>
  /// Some assumptions that don't show up in the dependency list
  /// are innocuous. In particular, `assume true` is often used
  /// as a place to attach attributes such as `{:split_here}`.
  /// Don't warn about such assumptions. Also don't warn about
  /// assumptions that aren't explicit (coming from `assume` or
  /// `assert` statements), for now, because they are difficult
  /// for the user to control.
  /// </summary>
  /// <param name="dep">the dependency to examine</param>
  /// <returns>false to skip warning about the absence of this
  /// dependency, true otherwise</returns>
  private static bool ShouldWarnUnused(ProofDependency dep) {
    if (dep is AssumptionDependency assumeDep) {
      if (assumeDep.Expr is not null &&
          Expression.IsBoolLiteral(assumeDep.Expr, out var lit) &&
          lit) {
        return false;
      }

      return assumeDep.WarnWhenUnused;
    }

    return true;
  }
}
