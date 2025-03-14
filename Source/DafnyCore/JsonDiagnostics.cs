#nullable enable

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Text.Json.Nodes;
using DafnyCore;
using VCGeneration;

namespace Microsoft.Dafny;

record DiagnosticMessageData(MessageSource source, ErrorLevel level, TokenRange Range, string? category, string message,
  IReadOnlyList<DafnyRelatedInformation> related) {
  private static JsonObject SerializePosition(Boogie.IToken tok, bool includeLength) {
    var addition = includeLength ? tok.val.Length : 0;
    return new JsonObject {
      ["pos"] = tok.pos + addition,
      ["line"] = tok.line,
      ["character"] = tok.col - 1 + addition
    };
  }

  private static JsonObject SerializeRange(TokenRange range) {
    return new JsonObject {
      ["start"] = SerializePosition(range.StartToken, false),
      ["end"] = SerializePosition(range.EndToken, range.InclusiveEnd)
    };
  }

  private static JsonObject SerializeToken(TokenRange range) {
    return new JsonObject {
      ["filename"] = range.StartToken.filename,
      ["uri"] = range.Uri!.AbsoluteUri,
      ["range"] = SerializeRange(range)
    };
  }

  private static int SerializeErrorLevel(ErrorLevel lvl) {
    return lvl switch {
      ErrorLevel.Error => 1,
      ErrorLevel.Warning => 2,
      ErrorLevel.Info => 4,
      _ => throw new ArgumentException()
    };
  }

  private static string SerializeMessage(string? category, string message) {
    return category == null ? message : $"{category}: {message}";
  }

  private static JsonObject SerializeRelated(TokenRange range, string message) {
    return new JsonObject {
      ["location"] = SerializeToken(range),
      ["message"] = message,
    };
  }

  public JsonNode ToJson() {
    var auxRelated = related.Select<DafnyRelatedInformation, JsonNode>(aux =>
      SerializeRelated(aux.Range, aux.Message));
    return new JsonObject {
      ["location"] = SerializeToken(Range),
      ["severity"] = SerializeErrorLevel(level),
      ["message"] = SerializeMessage(category, message),
      ["source"] = source.ToString(),
      ["relatedInformation"] = new JsonArray(auxRelated.ToArray())
    };
  }

  public void WriteJsonTo(TextWriter wr) {
    wr.WriteLine(ToJson().ToJsonString(new JsonSerializerOptions { WriteIndented = false }));
  }
}

public class DafnyJsonConsolePrinter(DafnyOptions options) : DafnyConsolePrinter(options) {
  public override void ReportBplError(Boogie.IToken tok, string message, bool error, TextWriter tw, string? category = null) {
    var level = error ? ErrorLevel.Error : ErrorLevel.Warning;
    var dafnyToken = BoogieGenerator.ToDafnyToken(tok);
    var relatedInformation = new List<DafnyRelatedInformation>();
    relatedInformation.AddRange(
      ErrorReporterExtensions.CreateDiagnosticRelatedInformationFor(dafnyToken, Options.Get(Snippets.ShowSnippets)));
    new DiagnosticMessageData(MessageSource.Verifier, level, dafnyToken.ReportingRange, category, message, relatedInformation).WriteJsonTo(tw);
  }

  public override void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true) {
    var related = errorInfo.Aux.Where(e =>
      !(skipExecutionTrace && (e.Category ?? "").Contains("Execution trace"))).Select(aei => new DafnyRelatedInformation(
      BoogieGenerator.ToDafnyToken(aei.Tok).ReportingRange, aei.FullMsg)).ToList();
    var dafnyToken = BoogieGenerator.ToDafnyToken(errorInfo.Tok);
    new DiagnosticMessageData(MessageSource.Verifier, ErrorLevel.Error,
      dafnyToken.ReportingRange, errorInfo.Category, errorInfo.Msg, related).WriteJsonTo(tw);
    tw.Flush();
  }
}

public class JsonConsoleErrorReporter(DafnyOptions options) : BatchErrorReporter(options) {
  public override bool MessageCore(DafnyDiagnostic dafnyDiagnostic) {
    if (!base.MessageCore(dafnyDiagnostic) ||
        (Options is not { PrintTooltips: true } && dafnyDiagnostic.Level == ErrorLevel.Info)) {
      return false;
    }

    var data = new DiagnosticMessageData(dafnyDiagnostic.Source, dafnyDiagnostic.Level, dafnyDiagnostic.Range,
      dafnyDiagnostic.Level == ErrorLevel.Error ? "Error" : null, dafnyDiagnostic.Message,
      dafnyDiagnostic.RelatedInformation);
    data.WriteJsonTo(Options.OutputWriter);
    return true;
  }
}