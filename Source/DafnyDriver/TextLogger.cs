using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny;

public class TextLogger {
  private TextWriter tw;
  private TextWriter outWriter;
  private ProofDependencyManager depManager;

  public TextLogger(ProofDependencyManager depManager, TextWriter outWriter) {
    this.depManager = depManager;
    this.outWriter = outWriter;
  }

  public void Initialize(Dictionary<string, string> parameters) {
    tw = parameters.TryGetValue("LogFileName", out string filename) ? new StreamWriter(filename) : outWriter;
  }

  public void LogResults(IEnumerable<DafnyConsolePrinter.ConsoleLogEntry> verificationResults) {
    foreach (var (implementation, result) in verificationResults.OrderBy(vr => (vr.Implementation.Tok.filename, vr.Implementation.Tok.line, vr.Implementation.Tok.col))) {
      tw.WriteLine("");
      tw.WriteLine($"Results for {implementation.Name}");
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
            $"      {cmd.Tok.filename}({cmd.Tok.line},{cmd.Tok.col}): {cmd.Description}");
        }
        if (vcResult.CoveredElements.Any()) {
          tw.WriteLine("");
          tw.WriteLine("    Proof dependencies:");
          var fullDependencies =
            vcResult
            .CoveredElements
            .Select(depManager.GetFullIdDependency)
            .OrderBy(dep => (dep.RangeString(), dep.Description));
          foreach (var dep in fullDependencies) {
            tw.WriteLine($"      {dep.RangeString()}: {dep.Description}");
          }
        }

      }
    }
    tw.Flush();
  }
}
