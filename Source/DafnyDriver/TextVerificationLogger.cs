using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Boogie;
using VC;

namespace Microsoft.Dafny;

public class TextVerificationLogger : IVerificationResultFormatLogger {
  private TextWriter output;
  private IDafnyOutputWriter fallbackWriter;
  private ProofDependencyManager depManager;

  public TextVerificationLogger(ProofDependencyManager depManager, IDafnyOutputWriter fallbackWriter) {
    this.depManager = depManager;
    this.fallbackWriter = fallbackWriter;
  }

  public void Initialize(Dictionary<string, string> parameters) {
    output = parameters.TryGetValue("LogFileName", out string filename) ? new StreamWriter(filename) : fallbackWriter.StatusWriter();
  }

  public void LogScopeResults(VerificationScopeResult scopeResult) {
    LogResults(depManager, output, scopeResult);
  }

  public static void LogResults(ProofDependencyManager proofDependencyManager, TextWriter textWriter, VerificationScopeResult scopeResult) {
    var verificationScope = scopeResult.Scope;
    var results = scopeResult.Results.Select(t => t.Result).ToList();
    var outcome = results.Aggregate(VcOutcome.Correct, (o, r) => JsonVerificationLogger.MergeOutcomes(o, r.Outcome));
    var runtime = results.Aggregate(TimeSpan.Zero, (a, r) => a + r.RunTime);
    textWriter.WriteLine("");
    textWriter.WriteLine($"Results for {verificationScope.Name}");
    textWriter.WriteLine($"  Overall outcome: {outcome}");
    textWriter.WriteLine($"  Overall time: {runtime}");
    textWriter.WriteLine($"  Overall resource count: {results.Sum(r => r.ResourceCount)}");
    // It doesn't seem possible to get a result with zero VCResults, but being careful with nulls just in case :)
    var maximumTime = results.MaxBy(r => r.RunTime).RunTime.ToString() ?? "N/A";
    var maximumResourceCount = results.MaxBy(r => r.ResourceCount).ResourceCount.ToString() ?? "N/A";
    textWriter.WriteLine($"  Maximum assertion batch time: {maximumTime}");
    textWriter.WriteLine($"  Maximum assertion batch resource count: {maximumResourceCount}");
    foreach (var taskResult in scopeResult.Results.OrderBy(r => r.Result.VcNum)) {
      var vcResult = taskResult.Result;
      textWriter.WriteLine("");
      textWriter.WriteLine($"  Assertion batch {vcResult.VcNum}:");
      textWriter.WriteLine($"    Outcome: {vcResult.Outcome}");
      if (taskResult.Task != null && taskResult.Task.Split.RandomSeed != 0) {
        textWriter.WriteLine($"    Random seed: {taskResult.Task.Split.RandomSeed}");
      }
      textWriter.WriteLine($"    Duration: {vcResult.RunTime}");
      textWriter.WriteLine($"    Resource count: {vcResult.ResourceCount}");
      textWriter.WriteLine("");
      textWriter.WriteLine("    Assertions:");
      foreach (var cmd in vcResult.Asserts) {
        textWriter.WriteLine(
          $"      {cmd.tok.filename}({cmd.tok.line},{cmd.tok.col}): {cmd.Description.SuccessDescription}");
      }

      if (vcResult.CoveredElements.Any() && vcResult.Outcome == SolverOutcome.Valid) {
        textWriter.WriteLine("");
        textWriter.WriteLine("    Proof dependencies:");
        var fullDependencies = proofDependencyManager.GetOrderedFullDependencies(vcResult.CoveredElements).ToList();
        foreach (var dep in fullDependencies) {
          textWriter.WriteLine($"      {dep.RangeString()}: {dep.Description}");
        }
        var allPotentialDependencies = proofDependencyManager.GetPotentialDependenciesForDefinition(verificationScope.Name);
        var fullDependencySet = fullDependencies.ToHashSet();
        var unusedDependencies = allPotentialDependencies.Where(dep => !fullDependencySet.Contains(dep));
        textWriter.WriteLine("");
        textWriter.WriteLine("    Unused by proof:");
        foreach (var dep in unusedDependencies) {
          textWriter.WriteLine($"      {dep.RangeString()}: {dep.Description}");
        }
      }

    }
    textWriter.Flush();
  }

  public async Task Flush() {
    await output.DisposeAsync();
  }
}
