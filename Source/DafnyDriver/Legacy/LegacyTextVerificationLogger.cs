using System.Collections.Generic;
using System.IO;
using System.Linq;
using DafnyDriver.Commands;

namespace Microsoft.Dafny;

public class LegacyTextVerificationLogger(ProofDependencyManager depManager, TextWriter outWriter) {
  private TextWriter tw;

  public void Initialize(Dictionary<string, string> parameters) {
    tw = parameters.TryGetValue("LogFileName", out string filename) ? new StreamWriter(filename) : outWriter;
  }

  public void LogResults(IEnumerable<DafnyConsolePrinter.ConsoleLogEntry> verificationResults) {
    foreach (var (implementation, result) in verificationResults.OrderBy(vr => (vr.Implementation.Tok.filename, vr.Implementation.Tok.line, vr.Implementation.Tok.col))) {
      var taskResults = result.VCResults.Select(LegacyJsonVerificationLogger.VCResultLogEntryToPartialVerificationRunResult).ToList();
      var scopeResult = new VerificationScopeResult(new VerificationScope(implementation.Name, implementation.Tok), taskResults);
      TextVerificationLogger.LogResults(depManager, outWriter, scopeResult);
    }
    tw.Flush();
  }
}
