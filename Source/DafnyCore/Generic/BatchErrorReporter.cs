using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class BatchErrorReporter : ErrorReporter {
  public Dictionary<ErrorLevel, List<DafnyDiagnostic>> AllMessagesByLevel;
  public readonly List<DafnyDiagnostic> AllMessages = new();

  public BatchErrorReporter(DafnyOptions options) : base(options) {
    ErrorsOnly = false;
    AllMessagesByLevel = new Dictionary<ErrorLevel, List<DafnyDiagnostic>> {
      [ErrorLevel.Error] = new(),
      [ErrorLevel.Warning] = new(),
      [ErrorLevel.Info] = new()
    };
  }

  public override bool Message(MessageSource source, ErrorLevel level, string errorId, IToken tok, string msg) {
    if (ErrorsOnly && level != ErrorLevel.Error) {
      // discard the message
      return false;
    }

    var dafnyDiagnostic = new DafnyDiagnostic(errorId, tok, msg, source, level, new List<DafnyRelatedInformation>());
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
