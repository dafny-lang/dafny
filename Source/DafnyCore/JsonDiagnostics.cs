﻿#nullable enable

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Text.Json.Nodes;
using VCGeneration;
using static Microsoft.Dafny.ErrorRegistry;

namespace Microsoft.Dafny;

record DiagnosticMessageData(MessageSource source, ErrorLevel level, Boogie.IToken tok, string? category, string message, List<ErrorInformation.AuxErrorInfo>? related) {
  private static JsonObject SerializePosition(Boogie.IToken tok) {
    return new JsonObject {
      ["pos"] = tok.pos,
      ["line"] = tok.line,
      ["character"] = tok.col - 1
    };
  }

  private static JsonObject SerializeRange(Boogie.IToken tok) {
    var range = new JsonObject {
      ["start"] = SerializePosition(tok),
    };
    var origin = BoogieGenerator.ToDafnyToken(true, tok);
    if (origin.IncludesRange) {
      range["end"] = SerializePosition(origin.EndToken);
    }
    return range;
  }

  private static JsonObject SerializeToken(Boogie.IToken tok) {
    return new JsonObject {
      ["filename"] = tok.filename,
      ["uri"] = ((IOrigin)tok).Uri.AbsoluteUri,
      ["range"] = SerializeRange(tok)
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

  private static JsonObject SerializeRelated(Boogie.IToken tok, string? category, string message) {
    return new JsonObject {
      ["location"] = SerializeToken(tok),
      ["message"] = SerializeMessage(category, message),
    };
  }

  private static IEnumerable<JsonNode> SerializeInnerTokens(Boogie.IToken tok) {
    while (tok is NestedOrigin nestedToken) {
      tok = nestedToken.Inner;
      var message = nestedToken.Message != null ? "Related location: " + nestedToken.Message : "Related location";
      yield return SerializeRelated(tok, null, message);
    }
  }

  private static IEnumerable<JsonNode> SerializeAuxInfo(ErrorInformation.AuxErrorInfo aux) {
    yield return SerializeRelated(aux.Tok, aux.Category, aux.Msg);
    foreach (var n in SerializeInnerTokens(aux.Tok)) {
      yield return n;
    }
  }

  public JsonNode ToJson() {
    var auxRelated = related?.SelectMany(SerializeAuxInfo) ?? [];
    var innerRelated = SerializeInnerTokens(tok);
    return new JsonObject {
      ["location"] = SerializeToken(tok),
      ["severity"] = SerializeErrorLevel(level),
      ["message"] = SerializeMessage(category, message),
      ["source"] = source.ToString(),
      ["relatedInformation"] = new JsonArray(auxRelated.Concat(innerRelated).ToArray())
    };
  }

  public void WriteJsonTo(TextWriter wr) {
    wr.WriteLine(ToJson().ToJsonString(new JsonSerializerOptions { WriteIndented = false }));
  }
}

public class DafnyJsonConsolePrinter : DafnyConsolePrinter {
  public override void ReportBplError(Boogie.IToken tok, string message, bool error, TextWriter tw, string? category = null) {
    var level = error ? ErrorLevel.Error : ErrorLevel.Warning;
    new DiagnosticMessageData(MessageSource.Verifier, level, tok, category, message, null).WriteJsonTo(tw);
  }

  public override void WriteErrorInformation(VCGeneration.ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true) {
    var related = errorInfo.Aux.Where(e =>
      !(skipExecutionTrace && (e.Category ?? "").Contains("Execution trace"))).ToList();
    new DiagnosticMessageData(MessageSource.Verifier, ErrorLevel.Error,
      errorInfo.Tok, errorInfo.Category, errorInfo.Msg, related).WriteJsonTo(tw);
    tw.Flush();
  }

  public DafnyJsonConsolePrinter(DafnyOptions options) : base(options) {
  }
}

public class JsonConsoleErrorReporter : BatchErrorReporter {
  protected override bool MessageCore(MessageSource source, ErrorLevel level, string errorID, Dafny.IOrigin tok, string msg) {
    if (base.MessageCore(source, level, errorID, tok, msg) && (Options is { PrintTooltips: true } || level != ErrorLevel.Info)) {
      new DiagnosticMessageData(source, level, tok, level == ErrorLevel.Error ? "Error" : null, msg, null).WriteJsonTo(Options.OutputWriter);
      return true;
    }

    return false;
  }

  public JsonConsoleErrorReporter(DafnyOptions options) : base(options) {
  }
}