#nullable enable
using System.IO;
using DafnyCore;
using VCGeneration;

namespace Microsoft.Dafny;

public class DafnyJsonConsolePrinter(DafnyOptions options) : DafnyConsolePrinter(options) {
  public override void ReportBplError(Boogie.IToken tok, string message, bool error, TextWriter tw, string? category = null) {
    var level = error ? ErrorLevel.Error : ErrorLevel.Warning;
    var dafnyToken = BoogieGenerator.ToDafnyToken(tok);
    var relatedInformation = new List<DafnyRelatedInformation>();
    relatedInformation.AddRange(
      ErrorReporterExtensions.CreateDiagnosticRelatedInformationFor(dafnyToken, Options.Get(Snippets.ShowSnippets)));
    new DiagnosticMessageData(MessageSource.Verifier, level, dafnyToken.ReportingRange, category, message, relatedInformation).WriteJsonTo(Options, tw);
  }

  public override void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true) {
    var related = errorInfo.Aux.Where(e =>
      !(skipExecutionTrace && (e.Category ?? "").Contains("Execution trace"))).Select(aei => new DafnyRelatedInformation(
      BoogieGenerator.ToDafnyToken(aei.Tok).ReportingRange, aei.FullMsg)).ToList();
    var dafnyToken = BoogieGenerator.ToDafnyToken(errorInfo.Tok);
    new DiagnosticMessageData(MessageSource.Verifier, ErrorLevel.Error,
      dafnyToken.ReportingRange, errorInfo.Category, errorInfo.Msg, related).WriteJsonTo(Options, tw);
    tw.Flush();
  }
}