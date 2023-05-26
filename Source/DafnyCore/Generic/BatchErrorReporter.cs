using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class BatchErrorReporter : ErrorReporter {
  public Dictionary<ErrorLevel, List<DafnyDiagnostic>> AllMessagesByLevel;

  public BatchErrorReporter(DafnyOptions options, DefaultModuleDefinition outerModule) : base(options, outerModule) {
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
    AllMessagesByLevel[level].Add(new DafnyDiagnostic(errorId, tok, msg, source, level, new List<DafnyRelatedInformation>()));
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
