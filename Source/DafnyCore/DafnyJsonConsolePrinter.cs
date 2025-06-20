#nullable enable
using System.IO;
using System.Collections.Generic;
using System.Linq;
using System.Text.Json;
using DafnyCore;
using VCGeneration;

namespace Microsoft.Dafny;

public class JsonConsoleErrorReporter(DafnyOptions options) : BatchErrorReporter(options) {
  public override bool MessageCore(DafnyDiagnostic dafnyDiagnostic) {
    if (!base.MessageCore(dafnyDiagnostic) ||
        (Options is not { PrintTooltips: true } && dafnyDiagnostic.Level == ErrorLevel.Info)) {
      return false;
    }

    var data = new DiagnosticMessageData(dafnyDiagnostic.Source, dafnyDiagnostic.Level, dafnyDiagnostic.Range,
      dafnyDiagnostic.Level == ErrorLevel.Error ? "Error" : null, "", dafnyDiagnostic.MessageParts,
      dafnyDiagnostic.RelatedInformation);
    _ = Options.OutputWriter.Status(data.ToJson(Options).ToJsonString(new JsonSerializerOptions { WriteIndented = false }));
    return true;
  }
}

public class DafnyJsonConsolePrinter(DafnyOptions options) : DafnyConsolePrinter(options) {
  public override void ReportBplError(Boogie.IToken tok, string message, bool error, TextWriter tw, string? category = null) {
    var level = error ? ErrorLevel.Error : ErrorLevel.Warning;
    var dafnyToken = BoogieGenerator.ToDafnyToken(tok);
    var relatedInformation = new List<DafnyRelatedInformation>();
    relatedInformation.AddRange(
      ErrorReporterExtensions.CreateDiagnosticRelatedInformationFor(dafnyToken, Options.Get(Snippets.ShowSnippets)));
    tw.WriteLine(new DiagnosticMessageData(MessageSource.Verifier, level, dafnyToken.ReportingRange, category,
        "", [message], relatedInformation).
      ToJson(Options).ToJsonString(new JsonSerializerOptions { WriteIndented = false }));
  }

  public override void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true) {
    var related = errorInfo.Aux.Where(e =>
      !(skipExecutionTrace && (e.Category ?? "").Contains("Execution trace"))).Select(aei => new DafnyRelatedInformation(
      BoogieGenerator.ToDafnyToken(aei.Tok).ReportingRange, "", [aei.FullMsg])).ToList();
    var dafnyToken = BoogieGenerator.ToDafnyToken(errorInfo.Tok);
    tw.WriteLine(new DiagnosticMessageData(MessageSource.Verifier, ErrorLevel.Error,
      dafnyToken.ReportingRange, errorInfo.Category, "", [errorInfo.Msg], related).
      ToJson(Options).ToJsonString(new JsonSerializerOptions { WriteIndented = false }));
    tw.Flush();
  }
}