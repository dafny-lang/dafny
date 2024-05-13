using System.Collections.Generic;
using System.Linq;
using DafnyCore;

namespace Microsoft.Dafny;

public class BatchErrorReporter : ErrorReporter {
  public Dictionary<ErrorLevel, List<DafnyDiagnostic>> AllMessagesByLevel;
  public readonly List<DafnyDiagnostic> AllMessages = new();

  public void CopyDiagnostics(ErrorReporter intoReporter) {
    foreach (var diagnostic in AllMessages) {
      intoReporter.Message(diagnostic.Phase, diagnostic.Level, diagnostic.ErrorId, diagnostic.Token, diagnostic.Message);
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

  protected override bool MessageCore(IPhase phase, ErrorLevel level, string errorId, IToken rootTok, string msg) {
    if (ErrorsOnly && level != ErrorLevel.Error) {
      // discard the message
      return false;
    }

    // TODO remove duplication with OER
    var relatedInformation = new List<DafnyRelatedInformation>();

    var usingSnippets = Options.Get(Snippets.ShowSnippets);
    if (rootTok is NestedToken nestedToken) {
      relatedInformation.AddRange(
        ErrorReporterExtensions.CreateDiagnosticRelatedInformationFor(
          nestedToken.Inner, nestedToken.Message, usingSnippets)
      );
    }

    var dafnyDiagnostic = new DafnyDiagnostic(phase, errorId, rootTok, msg, level, relatedInformation);
    AllMessages.Add(dafnyDiagnostic);
    AllMessagesByLevel[level].Add(dafnyDiagnostic);
    return true;
  }

  public override int Count(ErrorLevel level) {
    return AllMessagesByLevel[level].Count;
  }

  public override int CountExceptVerifierAndCompiler(ErrorLevel level) {
    return AllMessagesByLevel[level].Count(message => {
      var source = message.Phase.Source;
      return source != MessageSource.Verifier && source != MessageSource.Compiler;
    });
  }
}
