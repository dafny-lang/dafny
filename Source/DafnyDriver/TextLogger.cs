using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class TextLogger {
  private TextWriter tw;

  public void Initialize(Dictionary<string, string> parameters) {
    tw = parameters.TryGetValue("LogFileName", out string filename) ? new StreamWriter(filename) : Console.Out;
  }

  public void LogResults(List<(Implementation, VerificationResult)> verificationResults) {
    var orderedResults = verificationResults.OrderBy(vr => vr.Item1.VerboseName);
    foreach (var (implementation, result) in orderedResults) {
      tw.WriteLine("");
      tw.WriteLine($"Results for {implementation.VerboseName}");
      tw.WriteLine($"  Overall outcome: {result.Outcome}");
      tw.WriteLine($"  Overall time: {result.End - result.Start}");
      tw.WriteLine($"  Overall resource count: {result.ResourceCount}");
      // It doesn't seem possible to get a result with zero VCResults, but being careful with nulls just in case :)
      var maximumTime = result.VCResults.MaxBy(r => r.runTime)?.runTime.ToString() ?? "N/A";
      var maximumRC = result.VCResults.MaxBy(r => r.resourceCount)?.resourceCount.ToString() ?? "N/A";
      tw.WriteLine($"  Maximum assertion batch time: {maximumTime}");
      tw.WriteLine($"  Maximum assertion batch resource count: {maximumRC}");
      foreach (var vcResult in result.VCResults.OrderBy(r => r.vcNum)) {
        tw.WriteLine("");
        tw.WriteLine($"  Assertion batch {vcResult.vcNum}:");
        tw.WriteLine($"    Outcome: {vcResult.outcome}");
        tw.WriteLine($"    Duration: {vcResult.runTime}");
        tw.WriteLine($"    Resource count: {vcResult.resourceCount}");
        tw.WriteLine("");
        tw.WriteLine("    Assertions:");
        foreach (var cmd in vcResult.asserts) {
          tw.WriteLine(
            $"      {new Uri(cmd.tok.filename).AbsolutePath}({cmd.tok.line},{cmd.tok.col}): {cmd.Description.SuccessDescription}");
        }

      }
    }
    tw.Flush();
  }
}
