using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class BatchErrorReporter : ErrorReporter {
  public Dictionary<ErrorLevel, List<DafnyDiagnostic>> AllMessages;

  public BatchErrorReporter() {
    ErrorsOnly = false;
    AllMessages = new Dictionary<ErrorLevel, List<DafnyDiagnostic>> {
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
    AllMessages[level].Add(new DafnyDiagnostic(errorId, tok, msg, source));
    return true;
  }

  public override int Count(ErrorLevel level) {
    return AllMessages[level].Count;
  }

  public override int CountExceptVerifierAndCompiler(ErrorLevel level) {
    return AllMessages[level].Count(message => message.Source != MessageSource.Verifier &&
                                               message.Source != MessageSource.Compiler);
  }
}