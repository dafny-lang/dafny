using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class BatchErrorReporter : ErrorReporter {
  public Dictionary<ErrorLevel, List<DafnyDiagnostic>> AllMessagesByLevel;
  public readonly List<DafnyDiagnostic> AllMessages = [];

  public void CopyDiagnostics(ErrorReporter intoReporter) {
    foreach (var diagnostic in AllMessages) {
      intoReporter.MessageCore(diagnostic);
    }
  }

  public BatchErrorReporter(DafnyOptions options) : base(options) {
    ErrorsOnly = false;
    AllMessagesByLevel = new Dictionary<ErrorLevel, List<DafnyDiagnostic>> {
      [ErrorLevel.Error] = [],
      [ErrorLevel.Warning] = [],
      [ErrorLevel.Info] = []
    };
  }

  public override bool MessageCore(DafnyDiagnostic dafnyDiagnostic) {
    if (ErrorsOnly && dafnyDiagnostic.Level != ErrorLevel.Error) {
      // discard the message
      return false;
    }

    AllMessages.Add(dafnyDiagnostic);
    AllMessagesByLevel[dafnyDiagnostic.Level].Add(dafnyDiagnostic);
    return true;
  }

  public override int Count(ErrorLevel level) {
    return AllMessagesByLevel[level].Count;
  }

  public override int CountExceptVerifierAndCompiler(ErrorLevel level) {
    return AllMessagesByLevel[level].Count(message => message.Source != MessageSource.Verifier &&
                                               message.Source != MessageSource.Compiler);
  }
}
