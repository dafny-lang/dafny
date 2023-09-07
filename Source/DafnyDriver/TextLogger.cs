using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using VC;

namespace Microsoft.Dafny;

public class TextLogger {
  private TextWriter tw;
  private TextWriter outWriter;

  public TextLogger(TextWriter outWriter) {
    this.outWriter = outWriter;
  }

  public void Initialize(Dictionary<string, string> parameters) {
    tw = parameters.TryGetValue("LogFileName", out string filename) ? new StreamWriter(filename) : outWriter;
  }

  public void LogResults(IEnumerable<(string verboseName, (ConditionGeneration.Outcome outcome, TimeSpan time, int ressources, List<VCResult> vcResults) result)> verificationResults) {
    foreach (var (verboseName, result) in verificationResults.OrderBy(vr => vr.verboseName)) {
      tw.WriteLine("");
      tw.WriteLine($"Results for {verboseName}");
      tw.WriteLine($"  Overall outcome: {result.outcome}");
      tw.WriteLine($"  Overall time: {result.time}");
      tw.WriteLine($"  Overall resource count: {result.ressources}");
      // It doesn't seem possible to get a result with zero VCResults, but being careful with nulls just in case :)
      var maximumTime = result.vcResults.MaxBy(r => r.runTime)?.runTime.ToString() ?? "N/A";
      var maximumRC = result.vcResults.MaxBy(r => r.resourceCount)?.resourceCount.ToString() ?? "N/A";
      tw.WriteLine($"  Maximum assertion batch time: {maximumTime}");
      tw.WriteLine($"  Maximum assertion batch resource count: {maximumRC}");
      foreach (var vcResult in result.vcResults.OrderBy(r => r.vcNum)) {
        tw.WriteLine("");
        tw.WriteLine($"  Assertion batch {vcResult.vcNum}:");
        tw.WriteLine($"    Outcome: {vcResult.outcome}");
        tw.WriteLine($"    Duration: {vcResult.runTime}");
        tw.WriteLine($"    Resource count: {vcResult.resourceCount}");
        tw.WriteLine("");
        tw.WriteLine("    Assertions:");
        foreach (var cmd in vcResult.asserts) {
          tw.WriteLine(
            $"      {((IToken)cmd.tok).Filepath}({cmd.tok.line},{cmd.tok.col}): {cmd.Description.SuccessDescription}");
        }

      }
    }
    tw.Flush();
  }
}
