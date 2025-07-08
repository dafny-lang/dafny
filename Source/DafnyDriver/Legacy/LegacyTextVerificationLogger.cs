using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using DafnyDriver.Commands;

namespace Microsoft.Dafny;

public class LegacyTextVerificationLogger : IDisposable, IAsyncDisposable {
  private TextWriter tw;
  private IDafnyOutputWriter outWriter;
  private ProofDependencyManager depManager;

  public LegacyTextVerificationLogger(ProofDependencyManager depManager, IDafnyOutputWriter outWriter) {
    this.depManager = depManager;
    this.outWriter = outWriter;
  }

  public void Initialize(Dictionary<string, string> parameters) {
    tw = parameters.TryGetValue("LogFileName", out string filename) ? new StreamWriter(filename) : outWriter.StatusWriter();
  }

  public void LogResults(IEnumerable<DafnyConsolePrinter.ConsoleLogEntry> verificationResults) {
    foreach (var (implementation, result) in verificationResults.OrderBy(vr => (vr.Implementation.Tok.filename, vr.Implementation.Tok.line, vr.Implementation.Tok.col))) {
      var taskResults = result.VCResults.Select(LegacyJsonVerificationLogger.VCResultLogEntryToPartialVerificationRunResult).ToList();
      var scopeResult = new VerificationScopeResult(new VerificationScope(implementation.Name, implementation.Tok), taskResults);
      TextVerificationLogger.LogResults(depManager, tw, scopeResult);
    }
    tw.Flush();
  }

  public void Dispose() {
    tw?.Dispose();
  }

  public async ValueTask DisposeAsync() {
    if (tw != null) {
      await tw.DisposeAsync();
    }
  }
}
