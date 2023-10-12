using System.Linq;
using DafnyCore.Verifier;
using Microsoft.Dafny.ProofObligationDescription;
using VC;

namespace Microsoft.Dafny;

public class ProofDependencyWarnings {
  public static void WarnAboutSuspiciousDependencies(DafnyOptions dafnyOptions, ErrorReporter reporter, ProofDependencyManager depManager) {
    var verificationResults = (dafnyOptions.Printer as DafnyConsolePrinter).VerificationResults.ToList();
    var orderedResults =
      verificationResults.OrderBy(vr =>
        (vr.Implementation.Tok.filename, vr.Implementation.Tok.line, vr.Implementation.Tok.col));
    foreach (var (implementation, result) in orderedResults) {
      WarnAboutSuspiciousDependenciesForImplementation(dafnyOptions, reporter, depManager, implementation, result);
    }
  }

  public static void WarnAboutSuspiciousDependenciesForImplementation(DafnyOptions dafnyOptions, ErrorReporter reporter, ProofDependencyManager depManager, DafnyConsolePrinter.ImplementationLogEntry logEntry, DafnyConsolePrinter.VerificationResultLogEntry result) {
    if (result.Outcome != ConditionGeneration.Outcome.Correct) {
      return;
    }

    var potentialDependencies = depManager.GetPotentialDependenciesForDefinition(logEntry.Name);
    var usedDependencies =
      result
        .VCResults
        .SelectMany(vcResult => vcResult.CoveredElements.Select(depManager.GetFullIdDependency))
        .OrderBy(dep => (dep.RangeString(), dep.Description));
    var unusedDependencies =
      potentialDependencies
        .Except(usedDependencies)
        .OrderBy(dep => (dep.RangeString(), dep.Description));

    var unusedObligations = unusedDependencies.OfType<ProofObligationDependency>();
    var unusedRequires = unusedDependencies.OfType<RequiresDependency>();
    var unusedEnsures = unusedDependencies.OfType<EnsuresDependency>();
    var unusedAssumeStatements =
      unusedDependencies
        .OfType<AssumptionDependency>()
        .Where(d => d is AssumptionDependency ad && ad.IsAssumeStatement);
    if (dafnyOptions.Get(CommonOptionBag.WarnContradictoryAssumptions)) {
      foreach (var dep in unusedObligations) {
        if (ShouldWarnVacuous(dafnyOptions, logEntry.Name, dep)) {
          reporter.Warning(MessageSource.Verifier, "", dep.Range, $"proved using contradictory assumptions: {dep.Description}");
        }
      }

      foreach (var dep in unusedEnsures) {
        if (ShouldWarnVacuous(dafnyOptions, logEntry.Name, dep)) {
          reporter.Warning(MessageSource.Verifier, "", dep.Range, $"ensures clause proved using contradictory assumptions");
        }
      }
    }

    if (dafnyOptions.Get(CommonOptionBag.WarnRedundantAssumptions)) {
      foreach (var dep in unusedRequires) {
        reporter.Warning(MessageSource.Verifier, "", dep.Range, $"unnecessary requires clause");
      }

      foreach (var dep in unusedAssumeStatements) {
        if (ShouldWarnUnused(dep)) {
          reporter.Warning(MessageSource.Verifier, "", dep.Range, $"unnecessary assumption");
        }
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
    }

    // Ensures clauses are often proven vacuously during well-formedness checks.
    // There's unfortunately no way to identify these checks once Dafny has
    // been translated to Boogie other than looking at the name.
    if (verboseName.Contains("well-formedness") && dep is EnsuresDependency) {
      return false;
    }

    return true;
  }

  /// <summary>
  /// Some assumptions that don't show up in the dependency list
  /// are innocuous. In particular, `assume true` is often used
  /// as a place to attach attributes such as `{:split_here}`.
  /// Don't warn about such assumptions.
  /// </summary>
  /// <param name="dep">the dependency to examine</param>
  /// <returns>false to skip warning about the absence of this
  /// dependency, true otherwise</returns>
  private static bool ShouldWarnUnused(ProofDependency dep) {
    if (dep is AssumptionDependency assumeDep) {
      if (assumeDep.Expr is not null &&
          Expression.IsBoolLiteral(assumeDep.Expr, out var lit) &&
          lit == true) {
        return false;
      }
    }

    return true;
  }
}
