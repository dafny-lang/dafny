#nullable enable

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Text.Json.Nodes;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny;

record DiagnosticMessageData(MessageSource source, ErrorLevel level, Location tok,
  string? category, string message, IReadOnlyList<DafnyRelatedInformation> related) {
  private static JsonObject SerializePosition(Position position) {
    return new JsonObject {
      ["line"] = position.Line,
      ["character"] = position.Character
    };
  }

  private static JsonObject SerializeRange(Range range) {
    var result = new JsonObject {
      ["start"] = SerializePosition(range.Start),
      ["end"] = SerializePosition(range.End)
    };
    return result;
  }

  private static JsonObject SerializeLocation(Location tok) {
    return new JsonObject {
      ["filename"] = tok.Uri.Path,
      ["uri"] = tok.Uri.ToString(),
      ["range"] = SerializeRange(tok.Range)
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

  private static JsonObject SerializeRelated(Location location, string message) {
    return new JsonObject {
      ["location"] = SerializeLocation(location),
      ["message"] = message,
    };
  }

  public JsonNode ToJson() {
    var auxRelated = related.Select(aux => (JsonNode)SerializeRelated(aux.Location, aux.Message));
    return new JsonObject {
      ["location"] = SerializeLocation(tok),
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

public class DafnyJsonConsolePrinter : DafnyConsolePrinter {
  // public override void ReportBplError(Boogie.IToken tok, string message, bool error, TextWriter tw, string? category = null) {
  //   var level = error ? ErrorLevel.Error : ErrorLevel.Warning;
  //   new DiagnosticMessageData(MessageSource.Verifier, level, tok, category, message, null).WriteJsonTo(tw);
  // }

  public override void WriteErrorInformation(VCGeneration.ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true) {
    var related = errorInfo.Aux.Where(e =>
      !(skipExecutionTrace && (e.Category ?? "").Contains("Execution trace"))).Select(aei => new DafnyRelatedInformation(
      BoogieGenerator.ToDafnyToken(false, aei.Tok).Center, aei.FullMsg)).ToList();

    new DiagnosticMessageData(MessageSource.Verifier, ErrorLevel.Error,
      BoogieGenerator.ToDafnyToken(false, errorInfo.Tok).Center, errorInfo.Category, errorInfo.Msg, related).WriteJsonTo(tw);
    tw.Flush();
  }

  public DafnyJsonConsolePrinter(DafnyOptions options) : base(options) {
  }
}

public class JsonConsoleErrorReporter : BatchErrorReporter {
  public override bool MessageCore(DafnyDiagnostic dafnyDiagnostic) {
    if (base.MessageCore(dafnyDiagnostic) && (Options is { PrintTooltips: true } || dafnyDiagnostic.Level != ErrorLevel.Info)) {
      new DiagnosticMessageData(dafnyDiagnostic.Source, dafnyDiagnostic.Level, dafnyDiagnostic.Location!,
        dafnyDiagnostic.Level == ErrorLevel.Error ? "Error" : null, dafnyDiagnostic.Message, dafnyDiagnostic.RelatedInformation).WriteJsonTo(Options.OutputWriter);
      return true;
    }

    return false;
  }

  public JsonConsoleErrorReporter(DafnyOptions options) : base(options) {
  }
}