using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using DafnyDriver.Commands;
using Microsoft.Boogie;
using VC;

namespace Microsoft.Dafny;

public class TextVerificationLogger {
  private TextWriter tw;
  private TextWriter outWriter;
  private ProofDependencyManager depManager;

  public TextVerificationLogger(ProofDependencyManager depManager, TextWriter outWriter) {
    this.depManager = depManager;
    this.outWriter = outWriter;
  }

  public void Initialize(Dictionary<string, string> parameters) {
    tw = parameters.TryGetValue("LogFileName", out string filename) ? new StreamWriter(filename) : outWriter;
  }

  public void LogResults(IEnumerable<IGrouping<VerificationScope, VerificationRunResult>> implementationResults) {
    foreach (var group in implementationResults.OrderBy(vr => vr.Key.Token)) {
      var verificationScope = group.Key;
      var results = group.ToList();
      var outcome = results.Aggregate(VcOutcome.Correct, (o, r) => JsonVerificationLogger.MergeOutcomes(o, r.Outcome));
      var runtime = TimeSpan.FromSeconds(results.Sum(r => r.RunTime.Seconds));
      tw.WriteLine("");
      tw.WriteLine($"Results for {verificationScope.Name}");
      tw.WriteLine($"  Overall outcome: {outcome}");
      tw.WriteLine($"  Overall time: {runtime}");
      tw.WriteLine($"  Overall resource count: {results.Sum(r => r.ResourceCount)}");
      // It doesn't seem possible to get a result with zero VCResults, but being careful with nulls just in case :)
      var maximumTime = results.MaxBy(r => r.RunTime).RunTime.ToString() ?? "N/A";
      var maximumResourceCount = results.MaxBy(r => r.ResourceCount).ResourceCount.ToString() ?? "N/A";
      tw.WriteLine($"  Maximum assertion batch time: {maximumTime}");
      tw.WriteLine($"  Maximum assertion batch resource count: {maximumResourceCount}");
      foreach (var vcResult in results.OrderBy(r => r.VcNum)) {
        tw.WriteLine("");
        tw.WriteLine($"  Assertion batch {vcResult.VcNum}:");
        tw.WriteLine($"    Outcome: {vcResult.Outcome}");
        tw.WriteLine($"    Duration: {vcResult.RunTime}");
        tw.WriteLine($"    Resource count: {vcResult.ResourceCount}");
        tw.WriteLine("");
        tw.WriteLine("    Assertions:");
        foreach (var cmd in vcResult.Asserts) {
          tw.WriteLine(
            $"      {cmd.tok.filename}({cmd.tok.line},{cmd.tok.col}): {cmd.Description}");
        }

        if (vcResult.CoveredElements.Any() && vcResult.Outcome == SolverOutcome.Valid) {
          tw.WriteLine("");
          tw.WriteLine("    Proof dependencies:");
          var fullDependencies = depManager.GetOrderedFullDependencies(vcResult.CoveredElements).ToList();
          foreach (var dep in fullDependencies) {
            tw.WriteLine($"      {dep.RangeString()}: {dep.Description}");
          }
          var allPotentialDependencies = depManager.GetPotentialDependenciesForDefinition(verificationScope.Name);
          var fullDependencySet = fullDependencies.ToHashSet();
          var unusedDependencies = allPotentialDependencies.Where(dep => !fullDependencySet.Contains(dep));
          tw.WriteLine("");
          tw.WriteLine("    Unused by proof:");
          foreach (var dep in unusedDependencies) {
            tw.WriteLine($"      {dep.RangeString()}: {dep.Description}");
          }
        }

      }
    }
    tw.Flush();
  }
}
