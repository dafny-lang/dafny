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

  public void LogResults(IEnumerable<(string verboseName, DafnyConsolePrinter.VerificationResultLogEntry)> verificationResults) {
    foreach (var (verboseName, result) in verificationResults.OrderBy(vr => vr.verboseName)) {
      tw.WriteLine("");
      tw.WriteLine($"Results for {verboseName}");
      tw.WriteLine($"  Overall outcome: {result.Outcome}");
      tw.WriteLine($"  Overall time: {result.RunTime}");
      tw.WriteLine($"  Overall resource count: {result.ResourceCount}");
      // It doesn't seem possible to get a result with zero VCResults, but being careful with nulls just in case :)
      var maximumTime = result.VCResults.MaxBy(r => r.RunTime).RunTime.ToString() ?? "N/A";
      var maximumRC = result.VCResults.MaxBy(r => r.ResourceCount).ResourceCount.ToString() ?? "N/A";
      tw.WriteLine($"  Maximum assertion batch time: {maximumTime}");
      tw.WriteLine($"  Maximum assertion batch resource count: {maximumRC}");
      foreach (var vcResult in result.VCResults.OrderBy(r => r.VCNum)) {
        tw.WriteLine("");
        tw.WriteLine($"  Assertion batch {vcResult.VCNum}:");
        tw.WriteLine($"    Outcome: {vcResult.Outcome}");
        tw.WriteLine($"    Duration: {vcResult.RunTime}");
        tw.WriteLine($"    Resource count: {vcResult.ResourceCount}");
        tw.WriteLine("");
        tw.WriteLine("    Assertions:");
        foreach (var cmd in vcResult.Asserts) {
          tw.WriteLine(
            $"      {cmd.Tok.Filepath}({cmd.Tok.line},{cmd.Tok.col}): {cmd.Description}");
        }

      }
    }
    tw.Flush();
  }
}
