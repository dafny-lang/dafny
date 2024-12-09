using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class BatchErrorReporter : ErrorReporter {
  public Dictionary<ErrorLevel, List<DafnyDiagnostic>> AllMessagesByLevel;
  public readonly List<DafnyDiagnostic> AllMessages = new();

  public void CopyDiagnostics(ErrorReporter intoReporter) {
    foreach (var diagnostic in AllMessages) {
      intoReporter.Message(diagnostic.Source, diagnostic.Level, diagnostic.ErrorId, diagnostic.Token, diagnostic.Message);
    }
  }

  public BatchErrorReporter(DafnyOptions options) : base(options) {
    ErrorsOnly = false;
    AllMessagesByLevel = new Dictionary<ErrorLevel, List<DafnyDiagnostic>> {
      [ErrorLevel.Error] = new(),
      [ErrorLevel.Warning] = new(),
      [ErrorLevel.Info] = new()
    };
  }

  protected override bool MessageCore(MessageSource source, ErrorLevel level, string errorId, IOrigin tok, string msg) {
    if (ErrorsOnly && level != ErrorLevel.Error) {
      // discard the message
      return false;
    }

    var dafnyDiagnostic = new DafnyDiagnostic(source, errorId, tok, msg, level, new List<DafnyRelatedInformation>());
    AllMessages.Add(dafnyDiagnostic);
    AllMessagesByLevel[level].Add(dafnyDiagnostic);
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
