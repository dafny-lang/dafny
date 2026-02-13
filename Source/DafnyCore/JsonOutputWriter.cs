#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Threading.Tasks;

namespace Microsoft.Dafny;

class JsonOutputWriter(DafnyOptions options) : IDafnyOutputWriter {

  public void Debug(string message) {
    options.BaseOutputWriter.WriteLine(new JsonObject() {
      ["type"] = "debug",
      ["value"] = message
    }.ToJsonString());
  }

  public void Exception(string message) {
    options.BaseOutputWriter.WriteLine(new JsonObject() {
      ["type"] = "exception",
      ["value"] = message
    }.ToJsonString());
  }

  public Task Status(string message) {
    return WriteMessage(message, "status");
  }

  public Task Code(string message) {
    return WriteMessage(message, "code");
  }

  private Task WriteMessage(string message, string type) {
    return options.BaseOutputWriter.WriteLineAsync(new JsonObject() {
      ["type"] = type,
      ["value"] = message.Replace("\r\n", "\n")
    }.ToJsonString());
  }

  public TextWriter StatusWriter() {
    return new StringWriterWithDispose(s => WriteMessage(s, "status"));
  }

  public TextWriter ErrorWriter() {
    return new StringWriterWithDispose(s => WriteMessage(s, "error"));
  }

  public void WriteDiagnostic(DafnyDiagnostic dafnyDiagnostic) {
    var data = new DiagnosticMessageData(dafnyDiagnostic.Source, dafnyDiagnostic.Level, dafnyDiagnostic.Range,
      dafnyDiagnostic.Level == ErrorLevel.Error ? "Error" : null, dafnyDiagnostic.ErrorId, dafnyDiagnostic.MessageParts,
      dafnyDiagnostic.RelatedInformation);
    var jsonString = data.ToJsonMessage(options).ToJsonString(new JsonSerializerOptions { WriteIndented = false });
    options.BaseOutputWriter.WriteLine(jsonString);
  }

  public Task Error(string message) {
    return WriteMessage(message, "error");
  }
}

record DiagnosticMessageData(MessageSource Source, ErrorLevel Level, TokenRange Range, string? Category, string ErrorId, IReadOnlyList<object> MessageParts,
  IReadOnlyList<DafnyRelatedInformation> Related) {

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

  private static JsonObject SerializeToken(DafnyOptions options, TokenRange range) {
    return new JsonObject {
      ["filename"] = range.StartToken.filename,
      ["filePath"] = TokenExtensions.GetRelativeFilename(options, range.StartToken),
      ["uri"] = range.Uri?.AbsoluteUri ?? "file:///unknown",
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

  private static JsonObject SerializeRelated(DafnyOptions options, TokenRange range, string errorId, IReadOnlyList<object> messageParts) {
    if (options.Get(CommonOptionBag.JsonOutput)) {
      var formatMessage = DafnyDiagnostic.GetFormatMsgAndRemainingParts(errorId, ref messageParts);
      return new JsonObject {
        ["location"] = SerializeToken(options, range),
        ["arguments"] = new JsonArray(messageParts.Select(o => (JsonNode)JsonValue.Create(o.ToString())!).ToArray()),
        ["errorId"] = errorId,
        ["defaultFormatMessage"] = formatMessage,
      };
    }

    // Backwards compatibility case. Can be removed with the option --json-diagnostics
    return new JsonObject {
      ["location"] = SerializeToken(options, range),
      ["message"] = DafnyDiagnostic.MessageFromParts(errorId, messageParts),
    };
  }

  public JsonNode ToJson(DafnyOptions options) {
    var auxRelated = Related.Select<DafnyRelatedInformation, JsonNode>(aux =>
      SerializeRelated(options, aux.Range, aux.ErrorId, aux.MessageParts));

    if (options.Get(CommonOptionBag.JsonOutput)) {
      var messageParts = MessageParts;
      var formatMessage = DafnyDiagnostic.GetFormatMsgAndRemainingParts(ErrorId, ref messageParts);
      return new JsonObject {
        ["location"] = SerializeToken(options, Range),
        ["severity"] = SerializeErrorLevel(Level),
        ["arguments"] = new JsonArray(messageParts.Select(o => (JsonNode)JsonValue.Create(o.ToString())!).ToArray()),
        ["defaultFormatMessage"] = formatMessage,
        ["errorId"] = ErrorId,
        ["source"] = Source.ToString(),
        ["relatedInformation"] = new JsonArray(auxRelated.ToArray())
      };
    }

    // Backwards compatibility case. Can be removed with the option --json-diagnostics
    return new JsonObject {
      ["location"] = SerializeToken(options, Range),
      ["severity"] = SerializeErrorLevel(Level),
      ["message"] = SerializeMessage(Category, DafnyDiagnostic.MessageFromParts(ErrorId, MessageParts)),
      ["source"] = Source.ToString(),
      ["relatedInformation"] = new JsonArray(auxRelated.ToArray())
    };
  }

  public void WriteJsonTo(DafnyOptions options, TextWriter wr) {
    wr.WriteLine(ToJson(options).ToJsonString(new JsonSerializerOptions { WriteIndented = false }));
  }

  public JsonNode ToJsonMessage(DafnyOptions options) {
    return new JsonObject {
      ["type"] = "diagnostic",
      ["value"] = ToJson(options)
    };
  }
}