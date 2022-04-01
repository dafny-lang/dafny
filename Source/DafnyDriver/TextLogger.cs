using System;
using System.Collections.Generic;
using System.IO;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class TextLogger {
  private TextWriter tw;

  public void Initialize(Dictionary<string, string> parameters) {
    tw = parameters.TryGetValue("LogFileName", out string filename) ? new StreamWriter(filename) : Console.Out;
  }

  public void LogResults(List<(Implementation, VerificationResult)> verificationResults) {
    foreach (var (implementation, result) in verificationResults) {
      tw.WriteLine("");
      tw.WriteLine($"Results for {implementation.Name}");
      tw.WriteLine($"  Overall outcome: {result.Outcome}");
      tw.WriteLine($"  Overall time: {result.End - result.Start}");
      tw.WriteLine($"  Overall resource count: {result.ResourceCount}");
      foreach (var vcResult in result.VCResults) {
        tw.WriteLine("");
        tw.WriteLine($"  Assertion batch {vcResult.vcNum}:");
        tw.WriteLine($"    Outcome: {vcResult.outcome}");
        tw.WriteLine($"    Duration: {vcResult.runTime}");
        tw.WriteLine($"    Resource count: {vcResult.resourceCount}");
        tw.WriteLine("");
        tw.WriteLine("    Assertions:");
        foreach (var cmd in vcResult.asserts) {
          tw.WriteLine(
            $"      {cmd.tok.filename}({cmd.tok.line},{cmd.tok.col}): {cmd.Description.SuccessDescription}");
        }

      }
    }
    tw.Flush();
  }
}