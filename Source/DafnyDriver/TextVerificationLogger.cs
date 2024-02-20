using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using VC;

namespace Microsoft.Dafny;

public class TextVerificationLogger : IVerificationResultFormatLogger {
  private TextWriter output;
  private TextWriter fallbackWriter;
  private ProofDependencyManager depManager;

  public TextVerificationLogger(ProofDependencyManager depManager, TextWriter fallbackWriter) {
    this.depManager = depManager;
    this.fallbackWriter = fallbackWriter;
  }

  public void Initialize(Dictionary<string, string> parameters) {
    output = parameters.TryGetValue("LogFileName", out string filename) ? new StreamWriter(filename) : fallbackWriter;
  }

  public void LogScopeResults(VerificationScopeResult scopeResult) {
    var verificationScope = scopeResult.Scope;
    var results = scopeResult.Results.Select(t => t.Result).ToList();
    var outcome = results.Aggregate(VcOutcome.Correct, (o, r) => JsonVerificationLogger.MergeOutcomes(o, r.Outcome));
    var runtime = TimeSpan.FromSeconds(results.Sum(r => r.RunTime.Seconds));
    output.WriteLine("");
    output.WriteLine($"Results for {verificationScope.Name}");
    output.WriteLine($"  Overall outcome: {outcome}");
    output.WriteLine($"  Overall time: {runtime}");
    output.WriteLine($"  Overall resource count: {results.Sum(r => r.ResourceCount)}");
    // It doesn't seem possible to get a result with zero VCResults, but being careful with nulls just in case :)
    var maximumTime = results.MaxBy(r => r.RunTime).RunTime.ToString() ?? "N/A";
    var maximumResourceCount = results.MaxBy(r => r.ResourceCount).ResourceCount.ToString() ?? "N/A";
    output.WriteLine($"  Maximum assertion batch time: {maximumTime}");
    output.WriteLine($"  Maximum assertion batch resource count: {maximumResourceCount}");
    foreach (var vcResult in results.OrderBy(r => r.VcNum)) {
      output.WriteLine("");
      output.WriteLine($"  Assertion batch {vcResult.VcNum}:");
      output.WriteLine($"    Outcome: {vcResult.Outcome}");
      output.WriteLine($"    Duration: {vcResult.RunTime}");
      output.WriteLine($"    Resource count: {vcResult.ResourceCount}");
      output.WriteLine("");
      output.WriteLine("    Assertions:");
      foreach (var cmd in vcResult.Asserts) {
        output.WriteLine(
          $"      {cmd.tok.filename}({cmd.tok.line},{cmd.tok.col}): {cmd.Description.SuccessDescription}");
      }

      if (vcResult.CoveredElements.Any() && vcResult.Outcome == SolverOutcome.Valid) {
        output.WriteLine("");
        output.WriteLine("    Proof dependencies:");
        var fullDependencies = depManager.GetOrderedFullDependencies(vcResult.CoveredElements).ToList();
        foreach (var dep in fullDependencies) {
          output.WriteLine($"      {dep.RangeString()}: {dep.Description}");
        }
        var allPotentialDependencies = depManager.GetPotentialDependenciesForDefinition(verificationScope.Name);
        var fullDependencySet = fullDependencies.ToHashSet();
        var unusedDependencies = allPotentialDependencies.Where(dep => !fullDependencySet.Contains(dep));
        output.WriteLine("");
        output.WriteLine("    Unused by proof:");
        foreach (var dep in unusedDependencies) {
          output.WriteLine($"      {dep.RangeString()}: {dep.Description}");
        }
      }

    }
    output.Flush();
  }

  public void Flush() {
  }
}
